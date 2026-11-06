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
# Count the escaped JSON tool result, not source characters. Even another
# JSON encoding by the CLI has ample room under its 10,000-token limit:
# byte-level tokenization cannot use more tokens than serialized bytes.
PAGE_BYTES = 3000
RPC_BYTES = 6000
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
                relative = path.relative_to(ROOT).as_posix()
                try:
                    relative.encode("utf-8")
                    parts(relative)
                except (ValueError, UnicodeError):
                    continue
                yield relative
    if has_review:
        yield "review.md"


def tool_result(text):
    return {"content": [{"type": "text", "text": text}]}


def fits_page(value):
    # Read and search pages are JSON text inside the MCP text envelope.
    # Cursor/EOF metadata can grow after the last fragment was admitted.
    return len(json.dumps(tool_result(json.dumps(value))).encode()) <= PAGE_BYTES - 128


def integer(args, name, default=0):
    value = max(0, int(args.get(name, default)))
    if value > 2**63 - 1:
        raise ValueError("offset too large")
    return value


def longest_prefix(text, page):
    low, high = 0, len(text)
    while low < high:
        middle = (low + high + 1) // 2
        if fits_page(page(text[:middle])):
            low = middle
        else:
            high = middle - 1
    return low


def glob_matches(path, pattern):
    """Keep fnmatch's wildcards, allowing **/ segments to match no directory."""
    if fnmatch.fnmatchcase(path, pattern):
        return True
    chunks, start, index = [], 0, 0
    while index < len(pattern):
        if pattern[index] == "[":
            end = index + 1
            if end < len(pattern) and pattern[end] == "!":
                end += 1
            if end < len(pattern) and pattern[end] == "]":
                end += 1
            end = pattern.find("]", end)
            if end >= 0:
                index = end + 1
                continue
        if pattern.startswith("**/", index) and (index == 0 or pattern[index - 1] == "/"):
            chunks.append(pattern[start:index])
            index += 3
            start = index
        else:
            index += 1
    if not chunks:
        return False
    chunks.append(pattern[start:])
    names = path.split("/")
    count = len(names)
    following = [fnmatch.fnmatchcase("/".join(names[first:]), chunks[-1])
                 for first in range(count)]
    # Work backward through directory boundaries, without enumerating
    # every way to remove repeated **/ segments from the pattern.
    for prefix in reversed(chunks[:-1]):
        skipped = [False] * count
        for first in reversed(range(count)):
            skipped[first] = following[first] or (first + 1 < count and skipped[first + 1])
        if not prefix:
            following = skipped
            continue
        following = [any(skipped[end] and fnmatch.fnmatchcase(
            "/".join(names[first:end]) + "/", prefix)
            for end in range(first + 1, count)) for first in range(count)]
    return following[0]


def search_results(name, pattern, scope):
    for path in files():
        if scope and path != scope and not path.startswith(scope + "/"):
            continue
        if name == "Glob":
            if glob_matches(path, pattern):
                yield path
        else:
            try:
                yield from matches(path, pattern)
            except (OSError, ValueError):
                continue


def search_page(results, offset, column):
    chunks = []
    for index, text in enumerate(results):
        if index < offset:
            continue
        start = column if index == offset else 0
        if start > len(text):
            raise ValueError("column outside result")

        def page(fragment):
            stop = start + len(fragment)
            return {"matches": chunks + [{"offset": index, "column": start, "text": fragment}],
                    "next_offset": index + 1 if stop == len(text) else index,
                    "next_column": 0 if stop == len(text) else stop}

        count = longest_prefix(text[start:], page)
        if count == 0 and start < len(text):
            if not chunks:
                raise ValueError("page budget too small")
            return json.dumps({"matches": chunks, "next_offset": index, "next_column": start})
        fragment = text[start:start + count]
        current = page(fragment)
        chunks = current["matches"]
        if start + count < len(text):
            return json.dumps(current)
        # Reserve room for the end-of-results marker as well as a cursor.
        if not fits_page({"matches": chunks, "next_offset": None, "next_column": 0}):
            return json.dumps(current)
    return json.dumps({"matches": chunks, "next_offset": None, "next_column": 0})


def call(name, args):
    if not isinstance(args, dict):
        raise ValueError("arguments must be an object")
    if name == "Read":
        start = integer(args, "offset")
        count = min(PAGE_BYTES, max(1, integer(args, "limit", PAGE_BYTES)))
        with opened(args["path"]) as stream:
            stream.seek(start)
            data = stream.read(count)
            more = bool(stream.read(1))
        # Match character prefixes to byte offsets, so UTF-8 continuation
        # never skips the bytes of a character split at a page boundary.
        text = data.decode("utf-8", "surrogateescape")
        if more and text and 0xDC80 <= ord(text[-1]) <= 0xDCFF:
            text = text.rstrip("".join(chr(i) for i in range(0xDC80, 0xDD00))) or text

        def page(fragment):
            stop = start + len(fragment.encode("utf-8", "surrogateescape"))
            return {"offset": start, "next_offset": stop if more or stop < start + len(data) else None,
                    "text": fragment.encode("utf-8", "surrogateescape").decode("utf-8", "replace")}

        count = longest_prefix(text, page)
        if count == 0 and text:
            raise ValueError("page budget too small")
        return json.dumps(page(text[:count]))
    if name in ("Grep", "Glob"):
        pattern = args["pattern"]
        if not isinstance(pattern, str) or len(pattern) > 1000:
            raise ValueError("invalid pattern")
        scope = "/".join(parts(args["path"])) if "path" in args else ""
        return search_page(search_results(name, pattern, scope), integer(args, "offset"),
                           integer(args, "column"))
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
    tool("Grep", "Find literal text with file/line locations; path restricts to a relative file/directory. "
         "Follow next_offset/next_column as offset/column; matches may be split. No regex.",
         {"pattern": STRING, "path": STRING, "offset": {"type": "integer"},
          "column": {"type": "integer"}}, ["pattern"]),
    tool("Glob", "List checkout paths matching a glob; * can match directories, "
         "and **/ segments match zero or more directories. "
         "Follow next_offset/next_column as offset/column; long paths may be split.",
         {"pattern": STRING, "offset": {"type": "integer"}, "column": {"type": "integer"}}, ["pattern"]),
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
            if not isinstance(params, dict):
                raise ValueError("params must be an object")
            text = call(params["name"], params.get("arguments", {}))
            result = tool_result(text)
            if len(json.dumps(result).encode()) > PAGE_BYTES:
                raise ValueError("tool result too large")
            return result
        except (OSError, ValueError, KeyError, TypeError, OverflowError):
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
        encoded = json.dumps(reply)
        if len(encoded.encode()) > RPC_BYTES:
            # Includes discovery/errors, which contain no checkout text.
            encoded = json.dumps({"jsonrpc": "2.0", "id": None,
                                  "error": {"code": -32600, "message": "Request denied"}})
        print(encoded, flush=True)


if __name__ == "__main__":
    main()
