"""Finding 11: compiler-accepted conversion families must execute in HOL."""

from dataclasses import replace

import pytest


CONTRACT = """
@external
@pure
def bool_to_decimal(item: bool) -> decimal:
    return convert(item, decimal)

@external
@pure
def bool_to_bytes(item: bool) -> bytes1:
    return convert(item, bytes1)

@external
@pure
def decimal_to_bool(item: decimal) -> bool:
    return convert(item, bool)

@external
@pure
def decimal_to_bytes(item: decimal) -> bytes21:
    return convert(item, bytes21)

@external
@pure
def string_to_bool(item: String[8]) -> bool:
    return convert(item, bool)
"""


@pytest.mark.parametrize(
    "function,value,expected",
    [
        ("bool_to_decimal", True, 10**10),
        ("bool_to_bytes", True, b"\x01"),
        ("decimal_to_bool", -1, True),
        ("decimal_to_bytes", 1, bytes(20) + b"\x01"),
        ("string_to_bool", "\x00a", True),
    ],
)
def test_compiler_accepted_conversions(get_contract, compiler_settings, function, value, expected):
    settings = replace(compiler_settings, enable_decimals=True)
    contract = get_contract(CONTRACT, compiler_settings=settings)
    assert getattr(contract, function)(value) == expected
