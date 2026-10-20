"""Finding 24: expression operand order differs between compiler backends."""

import pytest


CONTRACT = """
counter: int256

@internal
def bump() -> int256:
    self.counter += 1
    return self.counter

@external
def comparison() -> bool:
    self.counter = 0
    return self.bump() < self.bump()

@external
def unsafe_subtraction() -> int256:
    self.counter = 0
    return unsafe_sub(self.bump(), self.bump())

@external
def unsafe_division() -> int256:
    self.counter = 0
    return unsafe_div(self.bump(), self.bump())

@external
def modular_power() -> uint256:
    self.counter = 0
    return pow_mod256(convert(self.bump(), uint256), convert(self.bump(), uint256))
"""


@pytest.mark.parametrize(
    "function,legacy,experimental",
    [
        ("comparison", False, True),
        ("unsafe_subtraction", 1, -1),
        ("unsafe_division", 2, 0),
        ("modular_power", 2, 1),
    ],
)
def test_effectful_operand_order(get_contract, experimental_codegen, function, legacy, experimental):
    expected = experimental if experimental_codegen else legacy
    assert getattr(get_contract(CONTRACT), function)() == expected
