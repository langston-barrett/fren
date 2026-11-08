"""Compile the real FFI definitions against the pinned compiler's emitted declarations.
No hand-declared expected prototypes. Called after the standalone Lake build.
"""
import hashlib
import os
import shlex
from pathlib import Path
import re
import subprocess

def check(here, real, work, source=None):
    # Every declared Heavy extern must have a generated declaration in its
    # corresponding module. A new source module must be built, not skipped.
    modules = {}
    sources = [(p, p.relative_to(here)) for p in here.rglob("*.lean")
               if not any(part.startswith(".") or part == "test-work" for part in p.relative_to(here).parts)]
    heavy = here.parent.parent / "src/Heavy"
    sources += [(p, Path("Heavy") / p.relative_to(heavy)) for p in heavy.rglob("*.lean")]
    for lean, module in sorted(sources):
        names = set(re.findall(r'@\[extern "(heavy_\w+)"\]', lean.read_text()))
        if names:
            modules[lean] = (module, names)
    assert modules, "no Heavy extern declarations found"
    selected = {}
    emitted_text = []
    for lean, (module, names) in modules.items():
        generated = here / ".lake/build/ir" / module.with_suffix(".c")
        text = generated.read_text()
        emitted_text.append(text)
        declarations = re.findall(r"^lean_object\* (heavy_\w+)\(([^;{}]*)\);$", text, re.M)
        found = dict(declarations)
        assert all(found[name] == args for name, args in declarations), (lean, declarations)
        assert names <= found.keys(), (lean, names - found.keys())
        for name in names:
            args = found[name]
            assert name not in selected or selected[name] == args, (name, args, selected[name])
            selected[name] = args
    text = "\n".join(emitted_text)
    selected = sorted(selected.items())
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
            "generated_sha256": hashlib.sha256(text.encode()).hexdigest(),
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
