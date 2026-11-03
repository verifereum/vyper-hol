#!/usr/bin/env python3
"""Build the native JSON bytecode parity runner with Poly/ML's polyc.

The runner links two generated programs: the compiler emitted by
compilerNativeEmitTheory and the JSON frontend's CV translation emitted by
vyperTestEmitTheory. Its sources are listed in bytecode_parity_json.mlb,
which MLton can also build; polyc gets the same files, in order, as `use`s.
"""

import argparse
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
NATIVE = ROOT / "lowering/defs/bytecode/native"
MLB = NATIVE / "bytecode_parity_json.mlb"
EXE = NATIVE / "bytecode_parity_json.exe"


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
    with tempfile.NamedTemporaryFile("w", suffix=".sml") as loader:
        for path in sources(MLB):
            loader.write(f'use "{path}";\n')
        loader.flush()
        subprocess.run(["polyc", "-o", str(EXE), loader.name], check=True)
    print(f"Built {EXE}", flush=True)


if __name__ == "__main__":
    main()
