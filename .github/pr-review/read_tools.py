"""A stdio MCP with only checkout reads and the fixed review.md write.

No subprocesses, regex evaluation, network, arbitrary resources or paths
outside the checkout. File opens reject links and nonregular files even
when called outside the workflow's sanitized, read-only mount.
"""
import fnmatch
from contextlib import contextmanager
import io
import json
import os
from pathlib import Path, PurePosixPath
import stat
import sys

ROOT = Path("/work")
OUTPUT = Path("/agent")
LIMIT = 200_000
REQUEST_LIMIT = 2_000_000
PRIVATE = {".git", ".codex", ".agents", ".claude"}


def parts(path):
    if not isinstance(path, str) or not path or "\\" in path:
        raise ValueError("invalid path")
    value = PurePosixPath(path)
    if value.is_absolute() or ".." in value.parts or PRIVATE.intersection(value.parts):
        raise ValueError("path outside readable checkout")
    return value.parts


@contextmanager
def opened(path):
    names = parts(path)
    if not names:
        raise ValueError("not a regular file")
    root = OUTPUT if path in ("review.md", "./review.md") and (OUTPUT / "review.md").exists() else ROOT
    directory = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for name in names[:-1]:
            child = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=directory)
            os.close(directory)
            directory = child
        fd = os.open(names[-1], os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=directory)
        with os.fdopen(fd, "rb") as stream:
            if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                raise ValueError("not a regular file")
            yield stream
    finally:
        os.close(directory)


def files():
    review = OUTPUT / "review.md"
    has_review = review.is_file() and not review.is_symlink()
    for directory, dirs, names in os.walk(ROOT, followlinks=False):
        dirs[:] = sorted(d for d in dirs if d not in PRIVATE
                         and not Path(directory, d).is_symlink())
        for name in sorted(names):
            path = Path(directory, name)
            if name not in PRIVATE and path.is_file() and not path.is_symlink():
                if path == ROOT / "review.md" and has_review:
                    continue
                yield path.relative_to(ROOT).as_posix()
    if has_review:
        yield "review.md"


def call(name, args):
    if name == "Read":
        start = max(0, int(args.get("offset", 0)))
        # JSON escaping can expand each byte up to six characters.
        count = min(LIMIT // 8, max(1, int(args.get("limit", LIMIT // 8))))
        with opened(args["path"]) as stream:
            stream.seek(start)
            data = stream.read(count)
            more = bool(stream.read(1))
        # Default-sized pages end between UTF-8 characters when the source
        # is valid UTF-8. Explicit arbitrary byte offsets still work.
        if more:
            try:
                data.decode("utf-8")
            except UnicodeDecodeError as error:
                if error.reason == "unexpected end of data" and error.start:
                    data = data[:error.start]
        return json.dumps({"offset": start, "next_offset": start + len(data) if more else None,
                           "text": data.decode("utf-8", "replace")}, ensure_ascii=False)
    if name in ("Grep", "Glob"):
        pattern = args["pattern"]
        if not isinstance(pattern, str) or len(pattern) > 1000:
            raise ValueError("invalid pattern")
        result, size, matched = [], 0, 0
        offset = max(0, int(args.get("offset", 0)))
        for path in files():
            if name == "Glob":
                lines = [path] if fnmatch.fnmatchcase(path, pattern) else []
            else:
                lines = matches(path, pattern)
            for line in lines:
                matched += 1
                if matched <= offset:
                    continue
                if size + len(line) + 1 > LIMIT:
                    return "\n".join(result) + f"\n[continue with offset={matched - 1}]"
                result.append(line)
                size += len(line) + 1
        return "\n".join(result)
    if name == "Write":
        if args["path"] not in ("review.md", "./review.md"):
            raise ValueError("only review.md is writable")
        text = args["content"]
        if not isinstance(text, str) or len(text.encode()) > REQUEST_LIMIT:
            raise ValueError("review too large")
        directory = os.open(OUTPUT, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
        try:
            fd = os.open("review.md", os.O_WRONLY | os.O_CREAT | os.O_TRUNC | os.O_NOFOLLOW
                         | os.O_NONBLOCK, 0o600, dir_fd=directory)
            with os.fdopen(fd, "w") as stream:
                if not stat.S_ISREG(os.fstat(stream.fileno()).st_mode):
                    raise ValueError("not a regular file")
                stream.write(text)
        finally:
            os.close(directory)
        return "Wrote review.md"
    raise ValueError("unknown tool")


def matches(path, pattern):
    """Stream bounded line fragments, retaining overlap for split matches."""
    with opened(path) as binary:
        stream = io.TextIOWrapper(binary, encoding="utf-8", errors="replace")
        number, overlap, found = 1, "", False
        while data := stream.readline(8192):
            text = overlap + data
            at = text.find(pattern)
            if at >= 0 and not found:
                yield f"{path}:{number}: {text[max(0, at - 1000):at + len(pattern) + 1000].rstrip()}"
                found = True
            if data.endswith("\n"):
                number, overlap, found = number + 1, "", False
            else:
                overlap = text[-max(1, len(pattern)):]


def tool(name, description, properties, required):
    return {"name": name, "description": description, "inputSchema": {
        "type": "object", "properties": properties, "required": required,
        "additionalProperties": False}}


STRING = {"type": "string"}
TOOLS = [
    tool("Read", "Read a checkout file. offset/limit are bytes; follow next_offset until null for the full file.",
         {"path": STRING, "offset": {"type": "integer"}, "limit": {"type": "integer"}}, ["path"]),
    tool("Grep", "Find literal text with file/line locations. offset skips matches for continuation; no regex.",
         {"pattern": STRING, "offset": {"type": "integer"}}, ["pattern"]),
    tool("Glob", "List checkout paths matching a glob; * can match directories.",
         {"pattern": STRING, "offset": {"type": "integer"}}, ["pattern"]),
    tool("Write", "Replace review.md with the complete review. No other path is writable.",
         {"path": STRING, "content": STRING}, ["path", "content"]),
]


def respond(request):
    method = request.get("method")
    if method == "initialize":
        return {"protocolVersion": "2024-11-05", "capabilities": {"tools": {}},
                "serverInfo": {"name": "fren-review", "version": "1"}}
    if method == "tools/list":
        return {"tools": TOOLS}
    if method == "resources/list":
        return {"resources": []}
    if method == "resources/templates/list":
        return {"resourceTemplates": []}
    if method == "ping":
        return {}
    if method == "tools/call":
        try:
            params = request["params"]
            text = call(params["name"], params.get("arguments", {}))
            return {"content": [{"type": "text", "text": text}]}
        except (OSError, ValueError, KeyError, TypeError):
            return {"isError": True, "content": [{"type": "text", "text": "Tool request denied"}]}
    raise ValueError("unknown method")


def main():
    while line := sys.stdin.buffer.readline(REQUEST_LIMIT + 1):
        if len(line) > REQUEST_LIMIT:
            raise ValueError("request too large")
        request = json.loads(line)
        if "id" not in request:
            continue
        reply = {"jsonrpc": "2.0", "id": request["id"]}
        try:
            reply["result"] = respond(request)
        except ValueError:
            reply["error"] = {"code": -32601, "message": "Method not allowed"}
        print(json.dumps(reply), flush=True)


if __name__ == "__main__":
    main()
