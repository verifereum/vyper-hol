#!/usr/bin/env python3
"""Emit or check pinned runtime IR for the external-entry witness corpus."""

import argparse
import hashlib
import json
from pathlib import Path

import vyper
from vyper.compiler.settings import OptimizationLevel, Settings
from vyper.venom import OPTIMIZATION_PASSES


def artifacts():
    here = Path(__file__).resolve().parent
    pin = (here.parents[3] / "VYPER_PIN").read_text().strip()
    commit = vyper.__commit__.strip()
    if len(commit) < 8 or not pin.startswith(commit):
        raise RuntimeError("Vyper does not match VYPER_PIN")
    if OPTIMIZATION_PASSES[OptimizationLevel.NONE] != OPTIMIZATION_PASSES[OptimizationLevel.O1]:
        raise RuntimeError("NONE no longer selects the pinned O1 Venom pipeline")
    settings = Settings(optimize=OptimizationLevel.NONE, evm_version="prague",
                        experimental_codegen=True)
    files = {}
    for source in sorted((here.parent / "external-entries/sources").glob("*.vy")):
        result = vyper.compile_code(
            source.read_text(), contract_path=Path(source.name),
            output_formats=("ir_runtime",), settings=settings,
            no_bytecode_metadata=True)
        header = (
            "; Pinned Vyper runtime IR reference.\n"
            f"; source: external-entries/sources/{source.name}\n"
            f"; source_sha256: {hashlib.sha256(source.read_bytes()).hexdigest()}\n"
            f"; vyper: {vyper.__version__}, commit {pin}\n"
            "; optimize=NONE (O1 Venom), prague, experimental_codegen=True, metadata=False\n"
        )
        files[f"{source.stem}.venom"] = header + str(result["ir_runtime"]).rstrip() + "\n"
    return here, files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--emit-json", action="store_true")
    group.add_argument("--check", action="store_true")
    args = parser.parse_args()
    here, files = artifacts()
    if args.emit_json:
        print(json.dumps(files))
        return
    stale = {p.name for p in here.glob("*.venom")} - files.keys()
    changed = [name for name, text in files.items()
               if not (here / name).is_file() or (here / name).read_text() != text]
    if stale or changed:
        raise SystemExit("Runtime IR fixtures differ: " + ", ".join(sorted(stale | set(changed))))
    print(f"Checked {len(files)} pinned runtime-IR fixtures")


if __name__ == "__main__":
    main()
