"""Execute the frozen Vyper bytecode and check observable return values."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
from dataclasses import asdict, dataclass
from importlib.metadata import version
from pathlib import Path

from eth.chains.base import MiningChain
from eth.db.atomic import AtomicDB
from eth.vm.forks.prague import PragueVM
from eth_hash.auto import keccak


@dataclass(frozen=True)
class Case:
    fixture: str
    signature: str
    arguments: tuple[int, ...]
    expected: int


CASES = (
    Case("pop_refill", "f()", (), 9),
    Case("conditional_snapshot", "f(bool)", (1,), 5),
    Case("conditional_snapshot", "f(bool)", (0,), 5),
    Case("conditional_memory_view", "f(bool)", (1,), 1),
    Case("conditional_memory_view", "f(bool)", (0,), 1),
    Case("nested_retained_pop", "f()", (), 5),
)


@dataclass(frozen=True)
class CaseResult:
    fixture: str
    signature: str
    arguments: tuple[int, ...]
    expected: int
    returned: int
    runtime_sha256: str


@dataclass(frozen=True)
class Report:
    python_version: str
    py_evm_version: str
    evm_version: str
    cases: tuple[CaseResult, ...]


def execute_case(oracle: Path, case: Case) -> CaseResult:
    fields = dict(
        line.split("=", 1)
        for line in (oracle / f"{case.fixture}.hex").read_text().splitlines()
    )
    runtime = bytes.fromhex(fields["runtime"])
    target, sender = b"\x11" * 20, b"\x33" * 20
    chain_type = MiningChain.configure(
        "LoadTimingWitness", vm_configuration=((0, PragueVM),), chain_id=1
    )
    chain = chain_type.from_genesis(
        AtomicDB(),
        {
            "difficulty": 0,
            "gas_limit": 30_000_000,
            "timestamp": 1,
            "base_fee_per_gas": 0,
        },
        {
            target: {"balance": 0, "nonce": 1, "code": runtime, "storage": {}},
            sender: {"balance": 10**20, "nonce": 0, "code": b"", "storage": {}},
        },
    )
    calldata = keccak(case.signature.encode())[:4] + b"".join(
        argument.to_bytes(32, "big") for argument in case.arguments
    )
    result = chain.get_vm().execute_bytecode(
        origin=sender,
        gas_price=0,
        gas=10_000_000,
        to=target,
        sender=sender,
        value=0,
        data=calldata,
        code=runtime,
        code_address=target,
    )
    if result.is_error:
        raise RuntimeError(f"{case.fixture}{case.arguments}: {result.error}")
    expected_bytes = case.expected.to_bytes(32, "big")
    if result.output != expected_bytes:
        raise AssertionError(
            f"{case.fixture}{case.arguments}: returned {result.output.hex()}, "
            f"expected {expected_bytes.hex()}"
        )
    return CaseResult(
        fixture=case.fixture,
        signature=case.signature,
        arguments=case.arguments,
        expected=case.expected,
        returned=int.from_bytes(result.output, "big"),
        runtime_sha256=hashlib.sha256(runtime).hexdigest(),
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    oracle = Path(__file__).parent / "oracle"
    results = tuple(execute_case(oracle, case) for case in CASES)
    report = Report(
        python_version=platform.python_version(),
        py_evm_version=version("py-evm"),
        evm_version="Prague",
        cases=results,
    )
    if args.output is not None:
        args.output.write_text(json.dumps(asdict(report), indent=2, sort_keys=True) + "\n")
    for result in results:
        print(f"PASS {result.fixture}{result.arguments}: {result.returned}")


if __name__ == "__main__":
    main()
