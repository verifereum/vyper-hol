#!/usr/bin/env python3
"""Build the native JSON bytecode parity runner with Poly/ML's polyc.

The runner links two generated programs: the compiler emitted by
compilerNativeEmitTheory and the JSON frontend's CV translation emitted by
vyperTestEmitTheory. Its sources are listed in bytecode_parity_json.mlb,
which MLton can also build; Poly/ML gets the same files, in order, as `use`s,
and polyc links the exported object.
"""

import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT / "bytecode/native"
MLB = NATIVE / "bytecode_parity_json.mlb"
EXE = NATIVE / "bytecode_parity_json.exe"
# Poly grows the heap to the cap: about 4.4 GB resident at 4096 MB. The
# compile also completes at 1500 MB, so this leaves headroom.
MAX_HEAP_MB = 4096


def sources(mlb):
    """The files an .mlb lists, nested .mlb files expanded, basis omitted."""
    for line in mlb.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("$(SML_LIB)"):
            continue
        path = (mlb.parent / line).resolve()
        if path.suffix == ".mlb":
            yield from sources(path)
        # polyc calls `main` itself; MLton needs the explicit call.
        elif not path.name.endswith("MLtonMain.sml"):
            yield path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--no-holbuild", action="store_true",
                        help="use the generated sources already on disk")
    args = parser.parse_args()
    if not args.no_holbuild:
        subprocess.run(
            ["holbuild", "build", "--skip-checkpoints", "--skip-proof-steps",
             "compilerNativeEmitTheory", "vyperTestEmitTheory"],
            cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory() as tmp:
        loader = Path(tmp) / "loader.sml"
        obj = Path(tmp) / "runner.o"
        loader.write_text("".join(f'use "{path}";\n' for path in sources(MLB)))
        # What polyc does, with a heap cap: Poly/ML's default maximum heap
        # is 80% of physical memory, which ignores the job's memory limit.
        subprocess.run(
            ["poly", "-q", "--error-exit", "--maxheap", str(MAX_HEAP_MB)],
            input=f'use "{loader}"; PolyML.export("{obj}", main);\n',
            text=True, check=True)
        subprocess.run(["polyc", "-o", str(EXE), str(obj)], check=True)
    print(f"Built {EXE}", flush=True)


if __name__ == "__main__":
    main()
