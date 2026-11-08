#!/usr/bin/env python3
"""Create a new owned, opt-in Lake overlay; never mutate the real toolchain.
Only immutable toolchain assets are delegated with symlinks, never caches.
This setup helper is not used by compiler invocations.
"""

import argparse
import os
import stat
from pathlib import Path
import shutil
import subprocess


def regular_bytes(path):
    fd = os.open(path, os.O_RDONLY | os.O_NONBLOCK | os.O_CLOEXEC)
    with os.fdopen(fd, "rb") as f:
        info = os.fstat(f.fileno())
        if not stat.S_ISREG(info.st_mode) or info.st_size > 67108864:
            raise ValueError("compiler and observer must be regular files at most 64 MiB")
        data = f.read(67108865)
        if len(data) != info.st_size:
            raise ValueError("compiler file changed or is incomplete")
        return data


def create(destination, real, observer):
    destination, real, observer = map(lambda p: Path(p).absolute(), (destination, real, observer))
    real, observer = real.resolve(strict=True), observer.resolve(strict=True)
    if regular_bytes(real) == regular_bytes(observer):
        raise ValueError("recursive overlay: real compiler is the observer")
    # Explicit path, never PATH or an overlay's discovery result at runtime.
    prefix = Path(subprocess.check_output([str(real), "--print-prefix"], text=True).strip()).resolve(strict=True)
    if real != (prefix / "bin/lean").resolve(strict=True):
        raise ValueError("real compiler must be the pinned installation's bin/lean")
    destination.mkdir(parents=True, exist_ok=False)
    (destination / "bin").mkdir()
    shutil.copy2(observer, destination / "bin/lean")
    (destination / "real-lean.path").write_text(str(real) + "\n")
    (destination / "records").mkdir(mode=0o700)
    # Read-only installed assets, not build outputs, packages or git metadata.
    for name in ("lib", "include", "share", "src"):
        if (prefix / name).exists():
            (destination / name).symlink_to(prefix / name, target_is_directory=True)
    for tool in (prefix / "bin").iterdir():
        if tool.name != "lean":
            (destination / "bin" / tool.name).symlink_to(tool)
    return destination


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--real-lean", required=True, type=Path)
    parser.add_argument("--observer", type=Path, default=Path(__file__).parent / ".lake/build/bin/heavy_observe")
    args = parser.parse_args()
    print(create(args.destination, args.real_lean, args.observer))


if __name__ == "__main__":
    main()
