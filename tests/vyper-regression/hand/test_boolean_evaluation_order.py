"""Which operands of `and`/`or` run, and in what order, with expected traces written by hand.

Rules, docs at VYPER_PIN:
- docs/types.rst:47-48, Booleans: "Short-circuiting of boolean operators (``or`` and
  ``and``) is consistent with the behavior of Python."
- docs/control-structures.rst:357, if statement: "The boolean is evaluated
  left-to-right, one expression at a time, until the condition is found to be
  true or false."

Each operand appends its digit to `trace`, so 12 means operand 1 ran, then operand 2.
"""

import pytest

CODE = """
trace: public(uint256)

@internal
def yes(k: uint256) -> bool:
    self.trace = self.trace * 10 + k
    return True

@internal
def no(k: uint256) -> bool:
    self.trace = self.trace * 10 + k
    return False

@external
def and_stops_at_false() -> uint256:
    self.trace = 0
    b: bool = self.no(1) and self.yes(2)
    return self.trace

@external
def and_runs_both() -> uint256:
    self.trace = 0
    b: bool = self.yes(1) and self.yes(2)
    return self.trace

@external
def or_stops_at_true() -> uint256:
    self.trace = 0
    b: bool = self.yes(1) or self.yes(2)
    return self.trace

@external
def or_runs_both() -> uint256:
    self.trace = 0
    b: bool = self.no(1) or self.yes(2)
    return self.trace

@external
def if_or_stops_when_true() -> uint256:
    self.trace = 0
    if self.no(1) or self.yes(2) or self.yes(3):
        pass
    return self.trace

@external
def if_and_stops_when_false() -> uint256:
    self.trace = 0
    if self.yes(1) and self.no(2) and self.yes(3):
        pass
    return self.trace
"""


# and_*/or_*: docs/types.rst:47-48 (Python short-circuiting: ``and`` stops at the first false
# operand, ``or`` at the first true one). if_*: docs/control-structures.rst:357 ("evaluated
# left-to-right, one expression at a time, until the condition is found to be true or false").
@pytest.mark.parametrize("function, trace", [
    ("and_stops_at_false", 1),
    ("and_runs_both", 12),
    ("or_stops_at_true", 1),
    ("or_runs_both", 12),
    ("if_or_stops_when_true", 12),
    ("if_and_stops_when_false", 12),
])
def test_boolean_operands_short_circuit_left_to_right(get_contract, function, trace):
    c = get_contract(CODE)
    assert getattr(c, function)() == trace
