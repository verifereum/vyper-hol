#!/usr/bin/env python3
"""Check pinned runtime-IR hashes, or regenerate the full IR for inspection."""

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
    group.add_argument("--output-dir", type=Path,
                       help="write the full runtime IR to this directory")
    args = parser.parse_args()
    here, files = artifacts()
    if args.emit_json:
        print(json.dumps(files))
        return
    if args.output_dir:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for name, text in files.items():
            (args.output_dir / name).write_text(text)
        print(f"Generated {len(files)} pinned runtime-IR fixtures in {args.output_dir}")
        return
    expected = json.loads((here / "sha256.json").read_text())
    stale = expected.keys() - files.keys()
    changed = [name for name, text in files.items()
               if expected.get(name) != hashlib.sha256(text.encode()).hexdigest()]
    if stale or changed:
        raise SystemExit("Runtime IR fixtures differ: " + ", ".join(sorted(stale | set(changed))))
    print(f"Checked {len(files)} pinned runtime-IR fixtures")


if __name__ == "__main__":
    main()
