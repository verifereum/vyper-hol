#!/usr/bin/env python3
"""Generate, probe and execute the differential witnesses of one corpus.

A corpus is a sibling directory (`memory-stores`, `external-calls`) with
`sources/`, `oracle/` and `parity-fixtures.txt`.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
from importlib.metadata import version
from pathlib import Path


def run(arguments: list[str], *, cwd: Path | None = None) -> str:
    return subprocess.run(arguments, cwd=cwd, check=True, text=True,
                          capture_output=True).stdout


def names(path: Path) -> list[str]:
    return [line for line in path.read_text().splitlines()
            if line and not line.startswith("#")]


def first_difference(left: bytes, right: bytes) -> int | None:
    for index, (a, b) in enumerate(zip(left, right)):
        if a != b:
            return index
    return min(len(left), len(right)) if len(left) != len(right) else None


def prepare(repo: Path, corpus: Path, output: Path, *, check: bool) -> None:
    """Export independent pinned-Vyper AST, layout and bytecode inputs."""
    pin = (repo / "VYPER_PIN").read_text().strip()
    compiler = run(["vyper", "--version"]).strip()
    if not compiler.endswith("commit." + pin[:8]):
        raise ValueError(f"Vyper {compiler} does not match VYPER_PIN {pin}")
    output.mkdir(parents=True, exist_ok=True)
    for source in sorted((corpus / "sources").glob("*.vy")):
        stem = source.stem
        raw = output / (stem + ".raw.json")
        raw.write_text(run(["vyper", "-f", "annotated_ast,layout", str(source)]))
        run(["python3", str(repo / "tests/sanitize_check_contract_json.py"),
             str(raw), str(output / (stem + ".json")), "--replace",
             str(source.parent) + "/="])
        raw.unlink()
        deploy, runtime = run([
            "vyper", "--experimental-codegen", "--evm-version", "prague",
            "-O", "none", "--disable-bytecode-metadata", "-f",
            "bytecode,bytecode_runtime", str(source)]).splitlines()
        (output / (stem + ".hex")).write_text(
            f"deploy={deploy.removeprefix('0x')}\n"
            f"runtime={runtime.removeprefix('0x')}\n")
    if check:
        for stem in names(corpus / "parity-fixtures.txt"):
            for extension in (".json", ".hex"):
                expected = corpus / "oracle" / (stem + extension)
                if expected.read_bytes() != (output / expected.name).read_bytes():
                    raise ValueError(f"independent oracle changed: {expected.name}")
    provenance = {
        "producer": "pinned Python Vyper",
        "vyper_commit": pin,
        "vyper_version": compiler,
        "python_version": platform.python_version(),
        "dependencies": {
            package: version(package)
            for package in ("cbor2", "immutables", "lark", "packaging",
                            "pycryptodome", "wheel")
        },
        "settings": {
            "experimental_codegen": True, "optimization_level": "NONE",
            "evm_version": "prague", "bytecode_metadata": False,
        },
        "sources": {
            source.name: hashlib.sha256(source.read_bytes()).hexdigest()
            for source in sorted((corpus / "sources").glob("*.vy"))
        },
        "outputs": {
            path.name: hashlib.sha256(path.read_bytes()).hexdigest()
            for path in sorted(output.iterdir())
            if path.suffix in (".hex", ".json") and path.name != "provenance.json"
        },
    }
    (output / "provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    if check:
        expected = json.loads((corpus / "oracle/provenance.json").read_text())
        retained = set(names(corpus / "parity-fixtures.txt"))
        provenance["outputs"] = {
            name: digest for name, digest in provenance["outputs"].items()
            if Path(name).stem in retained
        }
        if provenance != expected:
            raise ValueError("independent oracle provenance changed")


def probe(repo: Path, corpus: Path, fixtures: Path, output: Path,
          selected: list[str]) -> None:
    """Evaluate stock checker/compiler libraries and retain every outcome."""
    if output.resolve() == fixtures.resolve():
        raise ValueError("probe output must differ from the oracle fixture directory")
    output.mkdir(parents=True, exist_ok=True)
    if not selected:
        available = {path.stem for path in fixtures.glob("*.json")
                     if path.name != "provenance.json"}
        parity = names(corpus / "parity-fixtures.txt")
        selected = [stem for stem in parity if stem in available]
        selected += sorted(available - set(selected))
    for stem in selected:
        if not stem or Path(stem).name != stem:
            raise ValueError(f"witness name must be a file stem: {stem}")
        for extension in (".hex", ".term", ".residual"):
            (output / (stem + extension)).unlink(missing_ok=True)
    for filename in ("status.json", "summary.txt"):
        (output / filename).unlink(missing_ok=True)
    metadata = {
        "commit": run(["git", "rev-parse", "HEAD"], cwd=repo).strip(),
        "dirty_diff_sha256": hashlib.sha256(
            run(["git", "diff"], cwd=repo).encode()).hexdigest(),
        "lowering_sha256": {
            name: hashlib.sha256((repo / "lowering/defs" / name).read_bytes()).hexdigest()
            for name in ("contextScript.sml", "exprLoweringScript.sml",
                         "stmtLoweringScript.sml")
        },
        "diagnostic_timeout_seconds": 900,
        "fixtures": selected,
    }
    (output / "run.json").write_text(json.dumps(metadata, indent=2) + "\n")
    helper = Path(__file__).with_name("eval")
    script_id = hashlib.sha256(str(output.resolve()).encode()).hexdigest()
    script = repo / f".memory_store_{script_id}.sml"
    script.write_text(
        'fun loading name = (TextIO.output (TextIO.stdErr, "LOAD " ^ name ^ "\\n");\n'
        ' TextIO.flushOut TextIO.stdErr; load name);\n'
        'val _ = List.app loading ["compileVyperTheory", "supportedProgramTheory",\n'
        ' "concretizeMemLocDefsTheory", "codegenReadyComputeTheory",\n'
        ' "byteTheory", "optionTheory",\n'
        ' "vyperCheckContractFrontendLib",\n'
        ' "jsonASTLib", "finite_mapLib", "wordsLib", "Timeout"];\n'
        'open HolKernel Parse boolLib bossLib;\n'
        'val _ = computeLib.upd_compset finite_mapLib.add_finite_map_compset;\n'
        'val _ = computeLib.upd_compset (computeLib.add_thms\n'
        ' [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);\n' +
        (helper / "evalCompilerBytecodeLib.sml").read_text() + ";\n" +
        (helper / "memoryStoreWitnessLib.sml").read_text() + ";\n" +
        'fun bounded name =\n'
        ' (Timeout.apply (Time.fromSeconds 900)\n'
        f'  (memoryStoreWitnessLib.probe {json.dumps(str(fixtures))}\n'
        f'   {json.dumps(str(output))}) name\n'
        '  handle exn => memoryStoreWitnessLib.report\n'
        '   ("WITNESS " ^ name ^ " ERROR=" ^ General.exnMessage exn));\n'
        f'val _ = List.app bounded {json.dumps(selected)};\n')
    try:
        with (output / "probe.log").open("w") as log:
            completed = subprocess.run(["holbuild", "run", script.name], cwd=repo,
                                       stdout=log, stderr=subprocess.STDOUT)
    finally:
        script.unlink(missing_ok=True)
    if completed.returncode:
        raise RuntimeError(f"HOL probe failed: {output / 'probe.log'}")
    statuses: dict[str, list[str]] = {}
    for line in (output / "probe.log").read_text().splitlines():
        if line.startswith("WITNESS "):
            _, stem, status = line.split(" ", 2)
            statuses.setdefault(stem, []).append(status)
    (output / "status.json").write_text(json.dumps(statuses, indent=2) + "\n")
    lines = []
    for stem in selected:
        stages = "; ".join(statuses.get(stem, ["NO_RESULT"]))
        bytecode = output / (stem + ".hex")
        detail = ""
        if bytecode.exists():
            actual = read_runtime(bytecode)
            expected = read_runtime(fixtures / bytecode.name)
            detail = (f"; runtime bytes HOL={len(actual)} Vyper={len(expected)}"
                      f" first_diff={first_difference(actual, expected)}")
        line = stem + " " + stages + detail
        lines.append(line)
        print(line)
    (output / "summary.txt").write_text("\n".join(lines) + "\n")


def read_runtime(path: Path) -> bytes:
    line = next(line for line in path.read_text().splitlines()
                if line.startswith("runtime="))
    return bytes.fromhex(line.removeprefix("runtime="))


def execute(fixtures: Path, hol_output: Path) -> None:
    """Execute the two tuple-unpacking witnesses in py-evm's Prague VM."""
    from eth.chains.base import MiningChain
    from eth.db.atomic import AtomicDB
    from eth.vm.forks.prague import PragueVM
    from eth_abi import decode
    from eth_utils import keccak

    chain_type = MiningChain.configure(
        __name__="MemoryStoreWitnessChain", vm_configuration=((0, PragueVM),))
    cases = [
        ("t07_tuple_assign_string_elems", ["string"], ("ab",)),
        ("t08_tuple_assign_ret_type_mismatch", ["string", "uint256"], ("x", 3)),
    ]
    failed = False
    for stem, types, expected in cases:
        for label, root in [("Vyper", fixtures), ("HOL", hol_output)]:
            chain = chain_type.from_genesis(
                AtomicDB(), {"difficulty": 0, "gas_limit": 10_000_000,
                             "timestamp": 1}, {})
            computation = chain.get_vm().execute_bytecode(
                origin=b"\x01" * 20, sender=b"\x01" * 20,
                to=b"\x02" * 20, gas_price=0, gas=1_000_000, value=0,
                data=keccak(text="f()")[:4],
                code=read_runtime(root / (stem + ".hex")))
            if computation.is_error:
                print(stem, label, "ERROR", str(computation.error))
                failed = True
                continue
            actual = decode(types, computation.output)
            print(stem, label, actual)
            failed |= actual != expected
    if failed:
        raise ValueError("tuple-unpacking execution differed from the expected result")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode", choices=["prepare", "probe", "execute"])
    parser.add_argument("--corpus", default="memory-stores",
                        help="corpus directory next to this script")
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument("--fixtures", type=Path, required=True)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", action="store_true")
    parser.add_argument("--only", action="append", default=[])
    args = parser.parse_args()
    corpus = Path(__file__).with_name(args.corpus)
    if Path(args.corpus).name != args.corpus or not (corpus / "sources").is_dir():
        parser.error(f"unknown corpus: {args.corpus}")
    if args.mode == "prepare":
        prepare(args.repo.resolve(), corpus, args.fixtures.resolve(),
                check=args.check)
    elif args.output is None:
        parser.error("--output is required for probe and execute")
    elif args.mode == "probe":
        probe(args.repo.resolve(), corpus, args.fixtures.resolve(),
              args.output.resolve(), args.only)
    else:
        execute(args.fixtures.resolve(), args.output.resolve())


if __name__ == "__main__":
    main()
