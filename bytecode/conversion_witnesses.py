#!/usr/bin/env python3
"""Export pinned-Vyper checker inputs for conversions rejected by its codegen.

The parity fixtures use memory_store_witnesses.py instead: these controls
have annotated ASTs but intentionally have no Python bytecode oracle.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path


def run(arguments: list[str]) -> str:
    return subprocess.run(arguments, check=True, text=True,
                          capture_output=True).stdout


def prepare(repo: Path, output: Path, *, check: bool) -> None:
    """Export and optionally compare the independent checker inputs."""
    corpus = Path(__file__).with_name("conversions")
    pin = (repo / "VYPER_PIN").read_text().strip()
    compiler = run(["vyper", "--version"]).strip()
    if not compiler.endswith("commit." + pin[:8]):
        raise ValueError(f"Vyper {compiler} does not match VYPER_PIN {pin}")
    output.mkdir(parents=True, exist_ok=True)
    if any(output.iterdir()):
        raise ValueError("use an empty output directory")
    sources = sorted((corpus / "checker-sources").glob("*.vy"))
    for source in sources:
        raw = output / (source.stem + ".raw.json")
        raw.write_text(run(["vyper", "-f", "annotated_ast,layout", str(source)]))
        generated = output / (source.stem + ".json")
        run(["python3", str(repo / "tests/sanitize_check_contract_json.py"),
             str(raw), str(generated), "--replace", str(source.parent) + "/="])
        raw.unlink()
        if check and generated.read_bytes() != (
                corpus / "checker-oracle" / generated.name).read_bytes():
            raise ValueError(f"independent checker input changed: {generated.name}")
    provenance = {
        "producer": "pinned Python Vyper",
        "vyper_commit": pin,
        "vyper_version": compiler,
        "outputs": ["annotated_ast", "layout"],
        "sources": {source.name: hashlib.sha256(source.read_bytes()).hexdigest()
                    for source in sources},
        "inputs": {path.name: hashlib.sha256(path.read_bytes()).hexdigest()
                   for path in sorted(output.glob("*.json"))},
    }
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    if check and provenance != json.loads(
            (corpus / "checker-oracle/provenance.json").read_text()):
        raise ValueError("independent checker provenance changed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    prepare(args.repo.resolve(), args.output.resolve(), check=args.check)


if __name__ == "__main__":
    main()
