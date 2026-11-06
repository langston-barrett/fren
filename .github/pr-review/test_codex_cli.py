"""Exercise the pinned CLI's actual tools with a local fake model, no login.

The container test runs this with the production CLI/config/catalog. It
checks the real advertised schemas, not a mock of Codex's tool selection.
The model transport and its responses are fixtures, not live inference.
"""
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import os
from pathlib import Path
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


@unittest.skipUnless(shutil.which("codex"), "the container test installs the pinned CLI")
class CodexTools(unittest.TestCase):
    def test_advertised_tools(self):
        for kind in ("full", "fixes", "rebase"):
            with self.subTest(kind=kind):
                self.check_tools(effort(kind))

    def check_tools(self, reasoning):
        self.assertEqual(subprocess.check_output(["codex", "--version"], text=True).strip(), "codex-cli 0.166.0")
        requests = []

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
                # Only the test server's roots change. Production policy stays
                # fixed to /work and /agent, with the same tool implementation.
                shim = root / "mcp-fixture.py"
                shim.write_text("import sys\nfrom pathlib import Path\n"
                                f"sys.path.insert(0, {str(HERE)!r})\nimport read_tools\n"
                                f"read_tools.ROOT = Path({str(work)!r})\n"
                                f"read_tools.OUTPUT = Path({str(output)!r})\nread_tools.main()\n")
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
        finally:
            server.shutdown()
            server.server_close()
            thread.join()
        self.assertTrue(requests)
        self.assertEqual(len(requests), 4)
        outputs = {item["call_id"]: item["output"] for request in requests[1:] for item in request["input"]
                   if item["type"] == "function_call_output"}
        self.assertEqual(set(outputs), {"call_0", "call_1", "call_2", "call_3", "read", "write"})
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
