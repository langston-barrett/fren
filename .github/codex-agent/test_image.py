"""Check the installed image's lock with its cached public npm artifacts.

test_codex_sandbox.sh runs this inside the production image, offline.
The normal host-side unit suite skips it: it needs the image's npm cache.
"""
import base64
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import unittest


@unittest.skipUnless(os.environ.get("FREN_CODEX_IMAGE_TEST") == "1", "requires the built image")
class LockedImage(unittest.TestCase):
    def test_cached_install_accepts_the_lock_and_rejects_changed_integrity(self):
        installed = Path("/opt/codex")
        declared = json.loads((installed / "package.json").read_text())["dependencies"]["@openai/codex"]
        arch = {"x86_64": "x64", "aarch64": "arm64"}[platform.machine()]
        packages = ("@openai/codex", f"@openai/codex-linux-{arch}")
        for package in packages:
            with self.subTest(package=package), tempfile.TemporaryDirectory() as temp:
                root = Path(temp)
                project = root / "project"
                project.mkdir()
                home = root / "home"
                home.mkdir()
                env = dict(os.environ, CODEX_HOME=str(home))
                for name in ("package.json", "package-lock.json"):
                    shutil.copyfile(installed / name, project / name)
                cache = root / "cache"
                shutil.copytree("/root/.npm", cache, ignore=shutil.ignore_patterns("_logs"))
                command = ["npm", "ci", "--prefix", str(project), "--cache", str(cache),
                           "--offline", "--ignore-scripts", "--no-audit", "--no-fund"]
                good = subprocess.run(command, capture_output=True, text=True, timeout=120, env=env)
                self.assertEqual(good.returncode, 0, good.stdout + good.stderr)
                binary = str(project / "node_modules/.bin/codex")
                version = subprocess.check_output(
                    [binary, "--version"], text=True, timeout=30, env=env).strip()
                self.assertEqual(version, f"codex-cli {declared}")

                lock = project / "package-lock.json"
                data = json.loads(lock.read_text())
                data["packages"][f"node_modules/{package}"]["integrity"] = (
                    "sha512-" + base64.b64encode(bytes(64)).decode())
                lock.write_text(json.dumps(data))
                bad = subprocess.run(command, capture_output=True, text=True, timeout=120, env=env)
                if bad.returncode == 0:
                    # npm may skip a rejected optional platform package. The
                    # image's subsequent version check must still reject it.
                    bad = subprocess.run([binary, "--version"], capture_output=True,
                                         text=True, timeout=30, env=env)
                    self.assertNotEqual(bad.returncode, 0, "changed hash left a usable Codex")
                    self.assertIn("Missing optional dependency", bad.stderr)
                else:
                    self.assertRegex(bad.stdout + bad.stderr, r"\b(?:EINTEGRITY|ENOTCACHED)\b")


if __name__ == "__main__":
    unittest.main()
