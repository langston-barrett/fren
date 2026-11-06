"""Remove this run's container and fail unless its absence is confirmed."""
import os
import subprocess


def remove(name):
    subprocess.run(["docker", "rm", "--force", name], stdout=subprocess.DEVNULL,
                   stderr=subprocess.DEVNULL, check=False)
    remaining = subprocess.check_output([
        "docker", "ps", "--all", "--quiet", "--filter", f"name=^/{name}$"])
    if remaining.strip():
        raise RuntimeError("agent container still exists; withholding artifacts")


if __name__ == "__main__":
    remove(os.environ["CODEX_CONTAINER"])
