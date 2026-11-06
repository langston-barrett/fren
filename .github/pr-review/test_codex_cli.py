"""Exercise the pinned CLI's actual tools with a local fake model, no login.

The container test runs this with the production CLI/config/catalog. It
checks the real advertised schemas, not a mock of Codex's tool selection.
The model transport and its responses are fixtures, not live inference.
"""
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading
import unittest

from engine import effort
from check import comment

HERE = Path(__file__).resolve().parent
HEAD = "b" * 40
REVIEW = f"Review of {HEAD}: no blocking issues\n\nProbes: read the fixture checkout."


def mcp_text(value):
    if isinstance(value, list):
        value = "".join(block["text"] for block in value)
    if isinstance(value, str):
        # The pinned CLI prefixes MCP text with its own timing envelope.
        return re.sub(r"\AWall time: [0-9.]+ seconds\nOutput:", "", value, count=1)
    return "".join(block["text"] for block in value["content"])


@unittest.skipUnless(shutil.which("codex"), "the container test installs the pinned CLI")
class CodexTools(unittest.TestCase):
    def test_advertised_tools(self):
        for kind in ("full", "fixes", "rebase"):
            with self.subTest(kind=kind):
                self.check_tools(effort(kind), dense=kind == "full")

    def check_tools(self, reasoning, dense=False):
        self.assertEqual(subprocess.check_output(["codex", "--version"], text=True).strip(), "codex-cli 0.166.0")
        requests = []
        probes, errors = [], []
        plans = [("Read", {"path": "evidence/rows.txt"}),
                 ("Grep", {"pattern": "needle", "path": "evidence"}),
                 ("Glob", {"pattern": "evidence/*"})] if dense else []
        state = {"plan": 0, "last": None, "arguments": None}

        class Handler(BaseHTTPRequestHandler):
            def log_message(self, *_args):
                pass

            def do_POST(self):
                requests.append(json.loads(self.rfile.read(int(self.headers["Content-Length"]))))
                if len(requests) == 1:
                    items = [{"type": "function_call", "call_id": f"call_{i}", "name": name,
                              "arguments": json.dumps({"command": "touch escaped", "input": "x"})}
                             for i, name in enumerate(("exec_command", "apply_patch", "web.run",
                                                       "collaboration.spawn_agent"))]
                elif len(requests) == 2:
                    items = [{"type": "function_call", "call_id": "read", "name": "Read",
                              "namespace": "mcp__review", "arguments": json.dumps({"path": "fixture.txt"})}]
                elif len(requests) == 3:
                    items = [{"type": "function_call", "call_id": "write", "name": "Write",
                              "namespace": "mcp__review", "arguments": json.dumps({
                                  "path": "review.md", "content": REVIEW})}]
                else:
                    if state["last"]:
                        previous = next(item for item in requests[-1]["input"]
                                        if item["type"] == "function_call_output"
                                        and item["call_id"] == state["last"])
                        try:
                            page = json.loads(mcp_text(previous["output"]))
                            if page["next_offset"] is None:
                                state["plan"] += 1
                                state["arguments"] = None
                            else:
                                state["arguments"]["offset"] = page["next_offset"]
                                if "next_column" in page:
                                    state["arguments"]["column"] = page["next_column"]
                        except (ValueError, KeyError, TypeError) as error:
                            errors.append(type(error).__name__ + ": page was not intact JSON")
                            state["plan"] = len(plans)
                    if state["plan"] < len(plans):
                        name, arguments = plans[state["plan"]]
                        if state["arguments"] is None:
                            state["arguments"] = dict(arguments)
                        call_id = f"probe_{len(probes)}"
                        probes.append((call_id, name, dict(state["arguments"])))
                        state["last"] = call_id
                        items = [{"type": "function_call", "call_id": call_id, "name": name,
                                  "namespace": "mcp__review", "arguments": json.dumps(state["arguments"])}]
                    else:
                        items = [{"id": "msg_1", "type": "message", "role": "assistant",
                                  "content": [{"type": "output_text", "text": REVIEW}]}]
                events = [
                    ("response.created", {"response": {"id": "resp_1"}}),
                    *[("response.output_item.done", {"output_index": i, "item": item})
                      for i, item in enumerate(items)],
                    ("response.completed", {"response": {"id": "resp_1", "output": items,
                                                        "usage": {"input_tokens": 1, "output_tokens": 1,
                                                                  "total_tokens": 2}}}),
                ]
                self.send_response(200)
                self.send_header("Content-Type", "text/event-stream")
                self.end_headers()
                for event, data in events:
                    self.wfile.write(f"event: {event}\ndata: {json.dumps(dict(type=event, **data))}\n\n".encode())

        server = ThreadingHTTPServer(("127.0.0.1", 0), Handler)
        thread = threading.Thread(target=server.serve_forever, daemon=True)
        thread.start()
        try:
            with tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                auth, work, output = root / "auth", root / "work", root / "output"
                auth.mkdir()
                work.mkdir()
                output.mkdir()
                (work / "fixture.txt").write_text("fixture checkout source\n")
                # At least 20,000 separated short tokens, plus JSON escapes
                # and Unicode; the old single Grep response lost its middle.
                rows = [f"needle {i:04d} a b c d e f g h i j k l m n o p q r s t 一🙂 \"\\\x01"
                        for i in range(1000)]
                evidence = work / "evidence"
                evidence.mkdir()
                source = "\n".join(rows) + "\n"
                (evidence / "rows.txt").write_text(source)
                long = evidence
                for _ in range(20):
                    long /= "🙂" * 40
                long.mkdir(parents=True)
                long_source = "一" * 1000 + "needle" + "🙂" * 1000
                (long / "x").write_text(long_source)
                long_path = (long / "x").relative_to(work).as_posix()
                # Only the test server's roots change. Production policy stays
                # fixed to /work and /agent, with the same tool implementation.
                shim = root / "mcp-fixture.py"
                shim.write_text("import sys\nfrom pathlib import Path\n"
                                f"sys.path.insert(0, {str(HERE)!r})\nimport read_tools\n"
                                f"read_tools.ROOT = Path({str(work)!r})\n"
                                f"read_tools.OUTPUT = Path({str(output)!r})\n"
                                "original = read_tools.respond\n"
                                "def logged(request):\n result = original(request)\n"
                                " if request.get('method') == 'tools/call':\n"
                                f"  with open({str(output / 'calls.jsonl')!r}, 'a') as log:\n"
                                "   log.write(__import__('json').dumps(result) + '\\n')\n"
                                " return result\nread_tools.respond = logged\nread_tools.main()\n")
                config = (HERE / "codex.toml").read_text().replace("/trusted/pr-review", str(HERE))
                config = config.replace(json.dumps(str(HERE / "read_tools.py")), json.dumps(str(shim)))
                (auth / "config.toml").write_text(config)
                result = subprocess.run([
                    "codex", "exec", "--strict-config", "--ignore-rules", "--ephemeral",
                    "--skip-git-repo-check", "--model", "gpt-6.1-sol", "--json",
                    "--output-last-message", str(output / "last.md"),
                    "-c", 'model_provider="fixture"',
                    "-c", 'model_providers.fixture.name="fixture"',
                    "-c", f'model_providers.fixture.base_url="http://127.0.0.1:{server.server_port}"',
                    "-c", 'model_providers.fixture.wire_api="responses"',
                    "-c", 'model_providers.fixture.env_key="FIXTURE_KEY"',
                    "-c", f"model_reasoning_effort={reasoning}", "-"], input="Review the fixture.\n",
                    cwd=work, env={"PATH": os.environ["PATH"], "HOME": str(root),
                                   "CODEX_HOME": str(auth), "FIXTURE_KEY": "fixture-key"},
                    text=True, capture_output=True, timeout=60)
                self.assertEqual(result.returncode, 0, result.stderr + result.stdout)
                self.assertFalse((work / "escaped").exists())
                self.assertTrue((output / "review.md").exists(), result.stdout + result.stderr)
                self.assertEqual((output / "review.md").read_text(), REVIEW)
                self.assertEqual((output / "last.md").read_text().strip(), REVIEW)
                _, valid = comment((output / "review.md").read_text(), HEAD, "full", "URL", set())
                self.assertTrue(valid)
                self.assertFalse(errors, errors)
                returned = [json.loads(line) for line in (output / "calls.jsonl").read_text().splitlines()]
                outputs = {}
                for request in requests[1:]:
                    for item in request["input"]:
                        if item["type"] == "function_call_output":
                            outputs.setdefault(item["call_id"], item["output"])
                            # Include the actual CLI function-call envelope,
                            # escaped JSON, Unicode and all continuation data.
                            self.assertLess(len(json.dumps(item).encode()), 8000)
                ids = ["read", "write"] + [call_id for call_id, _, _ in probes]
                self.assertEqual(len(returned), len(ids))
                for call_id, expected in zip(ids, returned):
                    self.assertEqual(mcp_text(outputs[call_id]), mcp_text(expected), call_id)
                if dense:
                    read, matches, paths = "", {}, {}
                    for call_id, name, _ in probes:
                        page = json.loads(mcp_text(outputs[call_id]))
                        if name == "Read":
                            read += page["text"]
                        else:
                            collected = matches if name == "Grep" else paths
                            for chunk in page["matches"]:
                                prior = collected.setdefault(chunk["offset"], "")
                                self.assertEqual(chunk["column"], len(prior))
                                collected[chunk["offset"]] += chunk["text"]
                    self.assertEqual(read, source)
                    self.assertEqual([matches[i] for i in sorted(matches)],
                                     [f"evidence/rows.txt:{i + 1}: {row}" for i, row in enumerate(rows)]
                                     + [long_path + ":1: " + long_source])
                    self.assertEqual([paths[i] for i in sorted(paths)], ["evidence/rows.txt", long_path])
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
        self.assertTrue(requests)
        self.assertEqual(len(requests), 4 + len(probes))
        self.assertEqual(set(outputs), {"call_0", "call_1", "call_2", "call_3", "read", "write"}
                         | {call_id for call_id, _, _ in probes})
        for key in ("call_0", "call_1", "call_2", "call_3"):
            self.assertRegex(str(outputs[key]), "[Uu]n(recognized|supported)|[Uu]nknown")
        self.assertIn("fixture checkout source", str(outputs["read"]))
        self.assertIn("Wrote review.md", str(outputs["write"]))
        request = requests[0]
        self.assertEqual(request["model"], "gpt-6.1-sol")
        self.assertEqual(request["reasoning"]["effort"], reasoning)
        tools = request.get("tools", []) + [tool for item in request["input"]
                                           if item["type"] == "additional_tools" for tool in item["tools"]]
        # MCP resource listing exposes no resources. No shell, patch,
        # browser, image, delegation or arbitrary execution tool survives.
        names = set()
        for tool in tools:
            if tool["type"] == "namespace":
                for child in tool["tools"]:
                    self.assertEqual(child["type"], "function", child)
                    names.add(tool["name"] + "." + child["name"])
            else:
                self.assertEqual(tool["type"], "function", tool)
                names.add(tool["name"])
        self.assertEqual(names, {"mcp__review.Read", "mcp__review.Grep", "mcp__review.Glob",
                                "mcp__review.Write", "functions.list_mcp_resources",
                                "functions.list_mcp_resource_templates", "functions.read_mcp_resource"})


if __name__ == "__main__":
    unittest.main()
