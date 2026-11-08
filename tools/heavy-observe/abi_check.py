"""Compile the real FFI definitions against the pinned compiler's emitted declarations.
No hand-declared expected prototypes. Called after the standalone Lake build.
"""
import hashlib
import os
import shlex
from pathlib import Path
import re
import subprocess

NAMES = {"heavy_observe_wait", "heavy_observe_signal", "heavy_observe_write", "heavy_observe_read_regular"}


def check(here, real, work, source=None):
    emitted = here / ".lake/build/ir/Main.c"
    text = emitted.read_text()
    declarations = re.findall(r"^lean_object\* (heavy_observe_\w+)\(([^;{}]*)\);$", text, re.M)
    selected = [(name, args) for name, args in declarations if name in NAMES]
    assert len(selected) == 4 and {name for name, _ in selected} == NAMES, selected
    header = work / "emitted-ffi.h"
    header.write_text('#define _GNU_SOURCE\n#include <lean/lean.h>\n' + ''.join(
        f'lean_object* {name}({args});\n' for name, args in selected))
    source = source or here / "observer.c"
    command = [*shlex.split(os.environ.get("CC", "cc")), "-I", str(real.parent.parent / "include"),
               "-c", "-std=gnu17", "-Wall", "-Wextra", "-Werror",
               "-include", str(header), str(source), "-o", str(work / "abi-check.o")]
    result = subprocess.run(command, capture_output=True, timeout=15)
    (work / "abi-check.log").write_bytes(result.stdout + result.stderr)
    return {"command": command, "status": result.returncode, "declarations": selected,
            "generated_sha256": hashlib.sha256(emitted.read_bytes()).hexdigest(),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
