"""Python oracle for the linked-unit (multi-module) parity fixtures.

    PYTHONHASHSEED=0 python -P -s oracle.py OUT CASEDIR...

Compiles each CASEDIR/main.vy, its imports resolved in CASEDIR, with the
patched pinned Vyper on the path (see ../README.md: prague, experimental
codegen, OptimizationLevel.NONE, no bytecode metadata) and writes
OUT/<case>.json (annotated AST and layout, the native JSON runner's input) and
OUT/<case>.hex (deploy and runtime bytes).  Check them with
`native/bytecode_parity_json.exe OUT`.
"""
import json
import os
import sys
import warnings
from pathlib import Path

import vyper
from vyper.compiler.input_bundle import FilesystemInputBundle
from vyper.compiler.settings import OptimizationLevel, Settings


def main():
    out = Path(sys.argv[1]).resolve()
    out.mkdir(parents=True, exist_ok=True)
    # Resolve every case before the first chdir: the arguments are relative to
    # the starting directory.
    for case in [Path(a).resolve() for a in sys.argv[2:]]:
        os.chdir(case)  # some names are relative to the working directory
        settings = Settings(optimize=OptimizationLevel.NONE, evm_version="prague",
                            experimental_codegen=True, enable_decimals=True)
        with warnings.catch_warnings():
            warnings.simplefilter("ignore")
            r = vyper.compile_code(
                (case / "main.vy").read_text(), contract_path=Path("main.vy"),
                input_bundle=FilesystemInputBundle([case]),
                output_formats=("bytecode", "bytecode_runtime",
                                "annotated_ast_dict", "layout"),
                settings=settings, no_bytecode_metadata=True)
        frontend = r["annotated_ast_dict"] | r["layout"]
        # Imports resolve to absolute paths: keep the checkout's location out.
        text = json.dumps(frontend, separators=(",", ":"), sort_keys=True)
        (out / f"{case.name}.json").write_text(
            text.replace(str(case) + os.sep, "") + "\n")
        (out / f"{case.name}.hex").write_text(
            f"deploy={r['bytecode'].removeprefix('0x')}\n"
            f"runtime={r['bytecode_runtime'].removeprefix('0x')}\n")


if __name__ == "__main__":
    main()
