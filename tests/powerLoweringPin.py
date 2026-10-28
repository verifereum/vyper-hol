"""Check repaired integer power bounds against the authoritative Vyper pin.

Run with the pinned checkout on PYTHONPATH and its Python dependencies installed.
Raw non-byte widths are checked in powerTypedCounterexampleTheory, not rejected
from the HOL checker just because the Python frontend does not support them.
"""
from pathlib import Path
import subprocess

import vyper
from vyper.codegen.arithmetic import calculate_largest_base, calculate_largest_power
from vyper.compiler.settings import Settings
from vyper.exceptions import CompilerPanic, UnknownType


def exact_base(exponent, bits):
    limit = 1 << (bits - 1)
    lo, hi = 0, limit
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if mid**exponent < limit:
            lo = mid
        else:
            hi = mid
    lower = -(lo + 1) if exponent % 2 and (lo + 1)**exponent == limit else -lo
    return lower, lo


def exact_exponent(base, bits):
    limit = 1 << (bits - 1)
    exponent = 0
    while -limit <= base**(exponent + 1) < limit:
        exponent += 1
    return exponent


def run_backend_regressions():
    """Execute the pinned experimental (Venom) backend, not just compile it."""
    from eth.chains.base import MiningChain
    from eth.db.atomic import AtomicDB
    from eth.exceptions import Revert
    from eth.vm.forks.prague import PragueVM
    from eth_abi import encode
    from eth_utils import keccak

    chain = MiningChain.configure(__name__="PowerPinChain", vm_configuration=((0, PragueVM),))
    count = 0
    for typ, bases, exponents in (
        ("int256", [-2, 2, -(1 << 255), (1 << 255) - 1], [0, 1, 254, 255, 256, -1]),
        ("int8", [-128, -2, -1, 0, 1, 2, 127], [0, 1, 2, 7, 8, -1]),
        ("uint8", [0, 1, 2, 255], [0, 1, 2, 7, 8, 255]),
        ("uint256", [0, 1, 2], [0, 1, 255, 256]),
    ):
        signed = typ.startswith("int")
        bits = int(typ[3:] if signed else typ[4:])
        lower, upper = (-(1 << (bits - 1)), (1 << (bits - 1)) - 1) if signed else (0, (1 << bits) - 1)
        # Literal base: arbitrary typed runtime exponent, including negatives.
        # Literal exponent: only exponents the real frontend accepts.
        programs = [(f"({base}) ** x", base, None) for base in bases]
        programs += [(f"x ** {exponent}", None, exponent)
                     for exponent in exponents if 0 <= exponent <= bits - int(signed)]
        for expr, base_literal, exponent_literal in programs:
            source = f"@external\ndef f(x: {typ}) -> {typ}:\n    return {expr}\n"
            runtime = vyper.compile_code(source, settings=Settings(experimental_codegen=True),
                                         output_formats=["bytecode_runtime"])["bytecode_runtime"]
            arguments = exponents if base_literal is not None else bases
            for argument in arguments:
                if not lower <= argument <= upper:
                    continue
                base, exponent = ((base_literal, argument) if base_literal is not None
                                  else (argument, exponent_literal))
                value = pow(base, exponent) if exponent >= 0 else None
                expected = value if value is not None and lower <= value <= upper else None
                vm = chain.from_genesis(AtomicDB(),
                    {"difficulty": 0, "gas_limit": 10_000_000, "timestamp": 1}, {}).get_vm()
                result = vm.execute_bytecode(origin=b"\x01" * 20, sender=b"\x01" * 20,
                    to=b"\x02" * 20, gas_price=0, gas=1_000_000, value=0,
                    data=keccak(text=f"f({typ})")[:4] + encode([typ], [argument]),
                    code=bytes.fromhex(runtime.removeprefix("0x")))
                if expected is None:
                    assert result.is_error and isinstance(result.error, Revert), (typ, expr, argument)
                else:
                    assert not result.is_error, (typ, expr, argument, result.error)
                    assert int.from_bytes(result.output, "big", signed=signed) == expected, (typ, expr, argument)
                count += 1
    print(f"{count} pinned Venom-backend EVM executions passed: signed endpoints, overflow, -1/0/1 and 0**0")


def main():
    pin = (Path(__file__).resolve().parents[1] / "VYPER_PIN").read_text().strip()
    checkout = Path(vyper.__file__).resolve().parents[1]
    revision = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    assert revision == pin, (revision, pin)
    for bits in range(8, 257, 8):
        for exponent in range(2, bits):
            assert calculate_largest_base(exponent, bits, True) == exact_base(exponent, bits)
        limit = 1 << (bits - 1)
        for base in (-limit, -3, -2, 2, 3, limit - 1):
            assert calculate_largest_power(base, bits, True) == exact_exponent(base, bits)
    assert calculate_largest_base(255, 256, True) == (-2, 1)
    assert calculate_largest_power(-2, 256, True) == 255
    assert (-2)**255 == -(1 << 255)
    for bits in (1, 9):
        try:
            calculate_largest_base(2, bits, True)
        except CompilerPanic:
            pass
        else:
            raise AssertionError(f"pin unexpectedly accepts int{bits}")
    assert exact_base(2, 9) == (-15, 15)
    assert not -(1 << 8) <= (-16)**2 < (1 << 8)
    for expr, param in (("(-2) ** y", "y"), ("x ** 255", "x")):
        code = f"@external\ndef f({param}: int256) -> int256:\n    return {expr}\n"
        assert vyper.compile_code(
            code, settings=Settings(experimental_codegen=True), output_formats=["bytecode"]
        )["bytecode"]
    try:
        vyper.compile_code("@external\ndef f(x: int9) -> int9:\n    return x ** 2\n")
    except UnknownType:
        pass
    else:
        raise AssertionError("pin unexpectedly accepts int9 source annotations")
    print(f"Power bounds match Vyper {pin}; signed endpoint preserved; raw int9 overflows")
    run_backend_regressions()


if __name__ == "__main__":
    main()
