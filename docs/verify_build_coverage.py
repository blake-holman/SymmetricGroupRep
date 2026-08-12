#!/usr/bin/env python3
"""Check that every module is reachable from the root, so `lake build` sees it.

`lake build` only compiles what the root module transitively imports. A file that
is committed but imported by nothing is never compiled, so it can carry errors,
duplicate declarations, or unproved content indefinitely while the build stays
green.

This is not hypothetical here. `SemistandardHom.lean` -- 964 lines containing the
whole Sagan 2.10 development -- sat committed and orphaned across several
commits. It had two latent errors and a declaration duplicated from another
module, and none of it surfaced until the file was wired into the graph.

Usage:  python3 docs/verify_build_coverage.py
Exit status is non-zero if any module is unreachable.
"""

from __future__ import annotations

import pathlib
import re
import sys

ROOT = pathlib.Path("SymmetricGroupRep.lean")
PKG = pathlib.Path("SymmetricGroupRep")
IMPORT = re.compile(r"^import\s+(SymmetricGroupRep(?:\.[A-Za-z0-9_']+)*)\s*$", re.M)


def module_of(path: pathlib.Path) -> str:
    return "SymmetricGroupRep." + path.relative_to(PKG).with_suffix("").as_posix().replace("/", ".")


def path_of(module: str) -> pathlib.Path | None:
    if module == "SymmetricGroupRep":
        return ROOT
    candidate = PKG / (module.removeprefix("SymmetricGroupRep.").replace(".", "/") + ".lean")
    return candidate if candidate.exists() else None


def imports_of(path: pathlib.Path) -> list[str]:
    return IMPORT.findall(path.read_text(encoding="utf-8"))


def main() -> int:
    on_disk = {module_of(p) for p in PKG.rglob("*.lean")}

    reachable: set[str] = set()
    stack = ["SymmetricGroupRep"]
    while stack:
        module = stack.pop()
        if module in reachable:
            continue
        reachable.add(module)
        path = path_of(module)
        if path is None:
            continue
        stack.extend(imports_of(path))

    orphans = sorted(on_disk - reachable)

    print(f"{len(on_disk)} modules on disk; {len(on_disk & reachable)} reachable from the root")
    if orphans:
        print("\nORPHANED — committed but never compiled by `lake build`:")
        for module in orphans:
            print(f"  {module}")
        print("\nAdd an import to SymmetricGroupRep.lean, or delete the file.")
        return 1
    print("every module is in the build graph")
    return 0


if __name__ == "__main__":
    sys.exit(main())
