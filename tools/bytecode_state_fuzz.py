#!/usr/bin/env python3
"""Generate Vyper programs, capture py-evm state, and replay native HOL semantics.

The compiler checkout must be clean and match VYPER_PIN. This is independent of
bytecode parity: the reference is unmodified Vyper executing in pinned py-evm.

Use --source FILE --calls PLAN for an explicit scenario, or --replay-case
CASE/case.json to rerun its saved source and calls with the recorded import
directory, compiler settings and Python hash seed. External imports must remain
unchanged; traces.json remains the canonical exact native replay input.
Public runs launch the compiler worker with PYTHONHASHSEED=0 and retain
python_hash_seed in case.json and reference provenance. Saved-case replay honors
that seed, defaulting to 0 for older artifacts without the metadata.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import traceback

from bytecode_fuzz import Program

ROOT = Path(__file__).resolve().parents[1]
RUNNER = ROOT / "tests/.emit/run-test"
SMOKE_SOURCE = """event Changed:
    value: uint256

stored: uint256
scratch: transient(uint256)

@deploy
def __init__():
    self.stored = 3

@external
def update(x: uint256, fail: bool):
    self.stored = x
    self.scratch = x + 1
    log Changed(value=x)
    assert not fail
"""
SMOKE_CALLS = [
    {"function": "update", "args": [9, False]},
    {"function": "update", "args": [12, True]},
    {"function": "update", "args": [0, False]},
]


def generated_source(seed: str) -> str:
    """Keep Program's expressions, adding bounded full-world state operations."""
    return """state_initial: uint256
state_creations: uint256

@deploy
@payable
def __init__(initial: uint256):
    assert initial <= 32
    assert msg.value <= 128
    self.state_initial = initial

""" + Program(random.Random(seed)).generate() + """
@external
@payable
def state_fund():
    assert msg.value <= 32

@external
def state_send(recipient: address, amount: uint256):
    assert amount <= 16
    send(recipient, amount)

@external
@payable
def state_create(amount: uint256) -> address:
    assert msg.value <= 32
    assert amount <= 16
    assert self.state_creations < 2
    self.state_creations += 1
    return create_copy_of(self, value=amount)
"""


def generated_deployment(seed: str) -> dict:
    """Endow every generated deployment enough for its successful call prefix."""
    rng = random.Random(f"{seed}:deployment")
    return {"constructor_args": [rng.randint(1, 32)],
            "deployment_value": rng.randint(64, 128)}


def write_json(path: Path, value) -> None:
    path.write_text(json.dumps(value, indent=2) + "\n")


def abi_value(item: dict, rng: random.Random, addresses: tuple) -> object:
    """Produce boundary-heavy ABI values for bytecode_fuzz.Program's types."""
    ty = item["type"]
    array = re.fullmatch(r"(.+)\[([0-9]*)\]", ty)
    if array:
        element = {**item, "type": array[1]}
        # Program's only dynamic array type is DynArray[uint256, 3].
        length = int(array[2]) if array[2] else rng.randrange(4)
        return [abi_value(element, rng, addresses) for _ in range(length)]
    integer = re.fullmatch(r"(u?int)([0-9]+)", ty)
    if integer:
        bits = int(integer[2])
        low, high = ((0, 2**bits - 1) if integer[1] == "uint"
                     else (-2**(bits - 1), 2**(bits - 1) - 1))
        return rng.choice([low, low + 1, 0, 1, high - 1, high,
                           rng.randint(low, high)])
    if ty == "bool":
        return bool(rng.getrandbits(1))
    if ty == "address":
        return rng.choice(addresses)
    fixed_bytes = re.fullmatch(r"bytes([0-9]+)", ty)
    if fixed_bytes:
        return "0x" + rng.randbytes(int(fixed_bytes[1])).hex()
    raise ValueError(f"unsupported generated ABI type: {ty}")


def plan_calls(abi: list[dict], seed: str, count: int, addresses: tuple,
               *, generated: bool = False) -> list[dict]:
    rng = random.Random(seed)
    functions = [item for item in abi if item.get("type") == "function"]
    if not functions:
        raise ValueError("generated program has no external functions")
    prefix = []
    if generated:
        # ReferenceRun lists its funded EOAs first and the deployed contract last.
        # These small values succeed independently of Program's random arithmetic
        # and assertions, rather than hoping a full-width amount is affordable.
        amount = rng.randint(1, 16)
        prefix = [
            {"function": "state_fund", "args": [], "value": rng.randint(1, 32)},
            {"function": "state_send",
             "args": [rng.choice(addresses[:-1]), rng.randint(1, 16)]},
            {"function": "state_create", "args": [amount], "value": amount},
        ][:count]
        functions = [item for item in functions
                     if item["name"] not in ("state_fund", "state_send", "state_create")]
    rng.shuffle(functions)
    return prefix + [
        {"function": item["name"],
         "args": [abi_value(arg, rng, addresses) for arg in item["inputs"]]}
        for item in (functions[index % len(functions)]
                     for index in range(count - len(prefix)))
    ]


def load_scenario(path: Path) -> dict:
    scenario = json.loads(path.read_text())
    if not isinstance(scenario, dict) or not isinstance(scenario.get("calls"), list):
        raise ValueError("scenario must be an object containing a calls array")
    if not isinstance(scenario.get("constructor_args", []), list):
        raise ValueError("constructor_args must be an array")
    for call in scenario["calls"]:
        if (not isinstance(call, dict) or not isinstance(call.get("function"), str)
                or not isinstance(call.get("args", []), list)):
            raise ValueError("each call needs a function name and optional args array")
    return scenario


def reference_worker(config_path: Path) -> int:
    """A fresh, bounded process owns compiler imports and all reference state."""
    from bytecode_state_oracle import CompilerRejected, ReferenceRun, verify_vyper

    config = json.loads(config_path.read_text())
    directory = config_path.parent
    response = {"status": "reference-error", "checkpoints": 0}
    run = None
    try:
        response["provenance"] = verify_vyper(Path(config["vyper"]), ROOT)
        response["provenance"]["python_hash_seed"] = os.environ.get("PYTHONHASHSEED", "random")
        run = ReferenceRun(
            (directory / "source.vy").read_text(), name=config["name"],
            source_dir=Path(config["source_dir"]),
            constructor_args=config.get("constructor_args", []),
            value=config.get("deployment_value", 0),
            optimize=config["optimize"], experimental_codegen=config["experimental_codegen"],
        )
        calls = config["calls"]
        if calls is None:
            calls = ([] if run.contract is None else
                     plan_calls(run.abi, config["seed"], config["calls_per_case"],
                                run.addresses, generated=config.get("generated", False)))
        write_json(directory / "calls.json", {
            "constructor_args": config.get("constructor_args", []),
            "deployment_value": config.get("deployment_value", 0), "calls": calls,
        })
        # A failed deployment is an observed outcome, not a reference failure.
        # Keep any explicit plan as evidence, but compare only its constructor.
        if run.contract is not None:
            for call in calls:
                run.call(call)
        response["status"] = "passed"
    except CompilerRejected as error:
        response.update(status="compiler-rejected", error=str(error))
    except Exception:
        response["error"] = traceback.format_exc()
    finally:
        if run is not None:
            write_json(directory / "traces.json", run.traces)
            response["checkpoints"] = sum(
                trace.get("trace_type") == "state_checkpoint" for trace in run.traces
            )
        write_json(directory / "reference.json", response)
    return 0 if response["status"] in ("passed", "compiler-rejected") else 2


def native_outcome(returncode: int, stdout: str, stderr: str) -> str:
    """Reject process/protocol failures rather than reporting semantic mismatches."""
    try:
        rows = [json.loads(line) for line in stdout.splitlines()]
        if len(rows) == 1 and isinstance(rows[0], dict) and rows[0].get("name") == "case":
            if (rows[0].get("status") == "passed" and returncode == 0
                    and "error" not in rows[0] and not stderr):
                return "passed"
            if (rows[0].get("status") == "failed" and returncode == 1
                    and isinstance(rows[0].get("error"), str) and not stderr):
                return "mismatch"
    except (ValueError, TypeError):
        pass
    return "native-error"


def captured_text(value) -> str:
    return value.decode(errors="replace") if isinstance(value, bytes) else value or ""


def replay(binary: Path, traces: Path, timeout: float) -> dict:
    try:
        with traces.open() as stream:
            result = subprocess.run([str(binary)], stdin=stream, capture_output=True,
                                    text=True, timeout=timeout)
        return {"status": native_outcome(result.returncode, result.stdout, result.stderr),
                "returncode": result.returncode, "stdout": result.stdout, "stderr": result.stderr}
    except subprocess.TimeoutExpired as error:
        return {"status": "native-timeout", "returncode": None,
                "stdout": captured_text(error.stdout), "stderr": captured_text(error.stderr)}
    except OSError as error:
        return {"status": "native-error", "returncode": None, "stdout": "", "stderr": str(error)}


def run_case(directory: Path, config: dict, args, binary_digest: str) -> dict:
    config = {**config, "python_hash_seed": config.get("python_hash_seed", "0")}
    write_json(directory / "case.json", config)
    report = {"schema_version": 1, "name": config["name"], "seed": config["seed"],
              "settings": {key: config[key] for key in ("optimize", "experimental_codegen")},
              "native_sha256": binary_digest, "status": "reference-error", "checkpoints": 0}
    try:
        result = subprocess.run(
            [sys.executable, str(Path(__file__).resolve()),
             "--_reference-worker", str(directory / "case.json")],
            capture_output=True, text=True, timeout=args.reference_timeout,
            env={**os.environ, "PYTHONHASHSEED": str(config["python_hash_seed"])},
        )
        (directory / "reference.stdout").write_text(result.stdout)
        (directory / "reference.stderr").write_text(result.stderr)
        response = json.loads((directory / "reference.json").read_text())
        report.update(response)
        if result.returncode != 0:
            report["status"] = "reference-error"
        elif response["status"] == "passed":
            report["native"] = replay(args.runner, directory / "traces.json", args.timeout)
            report["status"] = report["native"]["status"]
    except subprocess.TimeoutExpired as error:
        report.update(status="reference-timeout", error="reference process exceeded timeout")
        (directory / "reference.stdout").write_text(captured_text(error.stdout))
        (directory / "reference.stderr").write_text(captured_text(error.stderr))
    except (OSError, ValueError, KeyError) as error:
        report.update(status="reference-error", error=str(error))
    write_json(directory / "report.json", report)
    return report


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--_reference-worker", type=Path, help=argparse.SUPPRESS)
    parser.add_argument("--vyper", type=Path,
                        help="clean compiler checkout matching VYPER_PIN")
    parser.add_argument("--runner", type=Path, default=RUNNER)
    parser.add_argument("--out", type=Path, help="new output directory (never overwrites a run)")
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--calls-per-case", type=int, default=6)
    parser.add_argument("--timeout", type=float, default=30, help="native timeout per case in seconds")
    parser.add_argument("--reference-timeout", type=float, default=60)
    parser.add_argument("--optimize", choices=("none", "gas", "codesize"), default="none")
    parser.add_argument("--codegen", choices=("venom", "legacy"), default="venom")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--smoke", action="store_true", help="exercise storage, transient state, logs and rollback")
    mode.add_argument("--source", type=Path, help="explicit Vyper source instead of generated programs")
    mode.add_argument("--replay-case", type=Path,
                      help="rerun saved case.json with sibling source.vy/calls.json and recorded settings")
    parser.add_argument("--calls", type=Path, help="JSON scenario for --source")
    args = parser.parse_args(argv)
    if args._reference_worker:
        return reference_worker(args._reference_worker)
    if args.out is None:
        parser.error("--out is required")
    if args.count < 1 or args.calls_per_case < 1 or args.timeout <= 0 or args.reference_timeout <= 0:
        parser.error("counts and timeouts must be positive")
    if bool(args.source) != bool(args.calls):
        parser.error("--source and --calls must be supplied together")
    args.runner = args.runner.resolve()
    saved = None
    if not args.runner.is_file():
        parser.error(f"native runner missing: {args.runner}; run tools/emit_run_test.py first")
    try:
        if args.replay_case:
            case_path = args.replay_case.resolve()
            saved = json.loads(case_path.read_text())
            scenario = load_scenario(case_path.parent / "calls.json")
            source = (case_path.parent / "source.vy").read_text()
        else:
            scenario = load_scenario(args.calls) if args.calls else {}
            source = args.source.read_text() if args.source else SMOKE_SOURCE if args.smoke else None
        args.vyper = (args.vyper or Path(saved["vyper"] if saved else ROOT / "vyper-ref")).resolve()
        with args.runner.open("rb") as stream:
            binary_digest = hashlib.file_digest(stream, "sha256").hexdigest()
        args.out = args.out.resolve()
        args.out.mkdir(parents=True, exist_ok=False)
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.error(str(error))
    counts = Counter()
    checkpoints = 0
    count = 1 if args.source or args.smoke or args.replay_case else args.count
    for index in range(count):
        seed = f"{args.seed}:{index}"
        name = f"state_{index:06d}"
        directory = args.out / name
        directory.mkdir()
        (directory / "source.vy").write_text(
            source if source is not None else generated_source(seed)
        )
        config = {
            "name": name, "seed": seed, "vyper": str(args.vyper),
            "source_dir": str(args.source.resolve().parent if args.source else ROOT),
            "optimize": args.optimize, "experimental_codegen": args.codegen == "venom",
            "calls_per_case": args.calls_per_case,
            "generated": source is None,
            "calls": scenario.get("calls", SMOKE_CALLS if args.smoke else None),
            **(generated_deployment(seed) if source is None else {
                "constructor_args": scenario.get("constructor_args", []),
                "deployment_value": scenario.get("deployment_value", 0),
            }),
        }
        if saved is not None:
            config = {
                **saved, "vyper": str(args.vyper),
                "calls": scenario["calls"],
                "constructor_args": scenario.get("constructor_args", saved.get("constructor_args", [])),
                "deployment_value": scenario.get("deployment_value", saved.get("deployment_value", 0)),
                "python_hash_seed": saved.get("python_hash_seed", "0"),
            }
        report = run_case(directory, config, args, binary_digest)
        counts[report["status"]] += 1
        checkpoints += report["checkpoints"]
        print(json.dumps({"case": name, "status": report["status"],
                          "checkpoints": report["checkpoints"]}), flush=True)
    compared = counts["passed"] + counts["mismatch"]
    operational = set(counts) - {"passed", "mismatch", "compiler-rejected"}
    exitcode = 2 if operational or not compared else 1 if counts["mismatch"] else 0
    summary = {"schema_version": 1, "counts": dict(counts), "compared": compared,
               "checkpoints": checkpoints, "exitcode": exitcode}
    write_json(args.out / "report.json", summary)
    print(json.dumps({"summary": summary, "out": str(args.out)}))
    return exitcode


if __name__ == "__main__":
    raise SystemExit(main())
