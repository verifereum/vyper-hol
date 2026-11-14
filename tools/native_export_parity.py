#!/usr/bin/env python3
"""Check compile_vyper's bytecode on every contract of the Vyper test exports.

The upstream test exports (tools/vyper_test_exports.py) are made with stock
VYPER_PIN, and their recorded bytes carry metadata, constructor arguments and
immutables. So the bytes compared here are not the exported ones: each
distinct contract source deployed at the oracle's profile (Venom, -O none,
prague) is compiled again, in this interpreter, by the patched pinned Vyper
that bytecode/python-o1-bytecode-fixtures installs, as
python_o1_bytecode_oracle.py --frontend writes a witness: annotated AST and
layout as <id>.json, deploy and runtime bytes without metadata as <id>.hex
(and the source as <id>.vy).
Deployments at other settings, and contracts of several modules (which the
runner does not compile), are counted, not compared.

bytecode/native/bytecode_parity_json.exe (tools/build_native_json_parity.py)
then compiles each JSON natively, and each contract gets a verdict:

  match        the bytes are equal
  mismatch     they differ, or compile_vyper failed, on a program in
               supported_program; fails the check unless listed in
               bytecode/native/export-known-mismatches.txt
  known        a listed mismatch
  seed         a mismatch, but Vyper produces HOL's bytes under another
               PYTHONHASHSEED (the compile runs with seed 0)
  outside      the program is outside supported_program; the detail gives
               the runner's result, which doesn't fail the check
  rejected     the HOL frontend rejected the program
  vyper-error  the patched pin doesn't compile the source at this profile
  error        the runner gave no supported_program verdict, or the known
               list is stale (a listed contract no longer mismatches or is
               gone); fails the check

Run it with the patched pin's Python and PYTHONHASHSEED=0:

  PYTHONHASHSEED=0 VENV/bin/python -I tools/native_export_parity.py \\
      tests/vyper-test-exports WORKDIR [--report FILE]
"""

from __future__ import annotations

import argparse
from collections import Counter
from concurrent.futures import ProcessPoolExecutor
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import warnings

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "bytecode/native/bytecode_parity_json.exe"
KNOWN = ROOT / "bytecode/native/export-known-mismatches.txt"
# The resolved compiler settings of a deployment at the oracle's profile.
ORACLE_SETTINGS = {"debug": False, "enable_decimals": True, "evm_version": "prague",
                   "experimental_codegen": True, "optimize": "none"}
OTHER_SEEDS = range(1, 8)
FAILING = ("mismatch", "error")
ORDER = FAILING + ("known", "seed", "vyper-error", "rejected", "outside", "match")


@dataclass
class Contract:
    id: str
    test: str
    source: str


@dataclass
class Verdict:
    contract: Contract
    verdict: str
    detail: str


def collect(exports: Path) -> tuple[list[Contract], Counter]:
    """The distinct single-module sources deployed at the oracle profile, and
    counts of the deployments left out, by reason."""
    contracts: dict[str, Contract] = {}
    skipped: Counter = Counter()
    for path in sorted(exports.rglob("*.json")):
        for item, export in json.loads(path.read_text()).items():
            for trace in export["traces"]:
                if trace["trace_type"] != "deployment":
                    continue
                if trace["deployment_type"] not in ("source", "blueprint"):
                    skipped[f"{trace['deployment_type']} deployments"] += 1
                elif not trace["deployment_succeeded"]:
                    skipped["failed deployments"] += 1
                elif trace["compiler_settings"] != ORACLE_SETTINGS:
                    skipped["deployments at other compiler settings"] += 1
                elif len(trace["solc_json"]["sources"]) != 1:
                    skipped["deployments of several modules"] += 1
                else:
                    source = trace["source_code"]
                    key = hashlib.sha256(source.encode()).hexdigest()[:16]
                    test = f"{path.relative_to(exports).with_suffix('')}::{item}"
                    contracts.setdefault(key, Contract(key, test, source))
    return list(contracts.values()), skipped


def compile_contract(source: str, path: Path) -> tuple[str, str]:
    """The witness JSON and .hex text of source, by the Vyper in this
    interpreter, as python_o1_bytecode_oracle.py --frontend writes them."""
    import vyper
    from vyper.compiler.settings import OptimizationLevel, Settings

    settings = Settings(optimize=OptimizationLevel.NONE, evm_version="prague",
                        experimental_codegen=True, enable_decimals=True)
    result = vyper.compile_code(
        source, contract_path=path,
        output_formats=("bytecode", "bytecode_runtime", "annotated_ast_dict", "layout"),
        settings=settings, no_bytecode_metadata=True)
    frontend = result["annotated_ast_dict"] | result["layout"]
    deploy = result["bytecode"].removeprefix("0x")
    runtime = result["bytecode_runtime"].removeprefix("0x")
    return (json.dumps(frontend, separators=(",", ":"), sort_keys=True) + "\n",
            f"deploy={deploy}\nruntime={runtime}\n")


def write_fixture(contract: Contract, work: Path) -> str | None:
    """Write <id>.vy, <id>.json and <id>.hex; the Vyper error if it doesn't
    compile."""
    from vyper.exceptions import VyperException

    (work / (contract.id + ".vy")).write_text(contract.source)
    try:
        with warnings.catch_warnings():  # deprecations in the upstream tests
            warnings.simplefilter("ignore")
            frontend, code = compile_contract(contract.source, Path(contract.id + ".vy"))
    except VyperException as e:
        return f"{type(e).__name__}: {str(e).splitlines()[0][:200]}"
    (work / (contract.id + ".json")).write_text(frontend)
    (work / (contract.id + ".hex")).write_text(code)
    return None


def seed_dependent(contract: Contract, native: Path) -> bool:
    """Whether Vyper produces the native bytes under another hash seed."""
    script = ("import sys, pathlib; sys.path.insert(0, sys.argv[1]);"
              "import native_export_parity as n;"
              "print(n.compile_contract(sys.stdin.read(), pathlib.Path(sys.argv[2]))[1], end='')")
    for seed in OTHER_SEEDS:
        code = subprocess.run(
            [sys.executable, "-I", "-c", script, str(ROOT / "tools"), contract.id + ".vy"],
            input=contract.source, capture_output=True, text=True, check=True,
            env={**os.environ, "PYTHONHASHSEED": str(seed)})
        if code.stdout == native.read_text():
            return True
    return False


def known_mismatches() -> dict[str, str]:
    """{contract id: reason} from export-known-mismatches.txt."""
    known = {}
    for line in KNOWN.read_text().splitlines():
        if line.strip() and not line.startswith("#"):
            key, reason = line.split()[:2]
            known[key] = reason
    return known


def classify(line: str) -> tuple[str, str, str]:
    """(id, verdict, detail) of a runner line, before the known list."""
    tag, rest = line.split(" ", 1)
    head, _, detail = rest.partition(": ")
    fields = head.split()
    supported = fields[2] if len(fields) > 2 else ""
    if tag == "REJECT":
        return fields[0], "rejected", detail
    if supported == "sp=F":
        return fields[0], "outside", detail or "bytes equal"
    if tag == "PASS":
        return fields[0], "match", ""
    if supported == "sp=T":
        return fields[0], "mismatch", detail
    return fields[0], "error", detail


def check(exports: Path, work: Path, jobs: int) -> tuple[list[Verdict], Counter]:
    """Each exported contract's verdict, and the deployments left out."""
    contracts, skipped = collect(exports)
    work.mkdir(parents=True, exist_ok=True)
    with ProcessPoolExecutor(jobs) as pool:
        errors = list(pool.map(write_fixture, contracts, [work] * len(contracts)))
    verdicts = [Verdict(c, "vyper-error", e) for c, e in zip(contracts, errors) if e]
    compiled = {c.id: c for c, e in zip(contracts, errors) if not e}
    native = work / "native"
    native.mkdir(exist_ok=True)
    runner = subprocess.run([str(RUNNER), str(work), *sorted(compiled)],
                            capture_output=True, text=True,
                            env={**os.environ, "NATIVE_PARITY_DUMP": str(native)})
    lines = [l for l in runner.stdout.splitlines() if l.startswith(("PASS ", "FAIL ", "REJECT "))]
    if len(lines) != len(compiled):
        raise SystemExit(f"runner gave {len(lines)} verdicts for {len(compiled)} contracts "
                         f"(exit {runner.returncode}):\n{runner.stderr[-2000:]}")
    known = known_mismatches()
    for line in lines:
        key, verdict, detail = classify(line)
        contract = compiled[key]
        dump = native / (key + ".hex")
        if verdict == "mismatch" and key in known:
            verdict, detail = "known", f"{known[key]}: {detail}"
        elif verdict == "mismatch" and dump.exists() and seed_dependent(contract, dump):
            verdict = "seed"
        elif key in known:
            verdict, detail = "error", f"listed ({known[key]}) but {verdict}; remove it from the list"
        verdicts.append(Verdict(contract, verdict, detail))
    for key in sorted(known.keys() - compiled.keys()):
        verdicts.append(Verdict(Contract(key, "-", ""), "error",
                                "listed but not exported; remove it from the list"))
    return verdicts, skipped


def report(verdicts: list[Verdict], skipped: Counter) -> str:
    """The per-contract report: counts, then one line per contract."""
    counts = Counter(v.verdict for v in verdicts)
    lines = [f"{len(verdicts)} contracts: "
             + ", ".join(f"{counts[k]} {k}" for k in ORDER if counts[k])]
    lines += [f"not compared: {n} {reason}" for reason, n in skipped.most_common()]
    for v in sorted(verdicts, key=lambda v: (ORDER.index(v.verdict), v.contract.test)):
        lines.append(f"{v.verdict:<11} {v.contract.id} {v.contract.test}"
                     + (f": {v.detail}" if v.detail else ""))
    return "\n".join(lines) + "\n"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("exports", type=Path, help="the test exports directory")
    parser.add_argument("work", type=Path, help="directory for the generated witnesses")
    parser.add_argument("--report", type=Path, help="also write the report here")
    parser.add_argument("--jobs", type=int, default=os.cpu_count())
    args = parser.parse_args()
    if os.environ.get("PYTHONHASHSEED") != "0":
        raise SystemExit("run with PYTHONHASHSEED=0: Vyper's bytes depend on it")
    import vyper
    pin = (ROOT / "VYPER_PIN").read_text().strip()
    if len(vyper.__commit__) < 8 or not pin.startswith(vyper.__commit__):
        raise SystemExit(f"this Python's Vyper is commit {vyper.__commit__}, not VYPER_PIN {pin}")
    if not RUNNER.exists():
        raise SystemExit(f"missing {RUNNER}; run tools/build_native_json_parity.py")
    verdicts, skipped = check(args.exports, args.work, args.jobs)
    text = report(verdicts, skipped)
    print(text, end="")
    if args.report:
        args.report.write_text(text)
    if any(v.verdict in FAILING for v in verdicts):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
