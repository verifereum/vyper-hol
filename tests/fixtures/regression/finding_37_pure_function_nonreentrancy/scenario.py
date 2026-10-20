"""Finding 37: pragma-default nonreentrancy does not protect pure functions."""

CONTRACT = """
# pragma nonreentrancy on

@external
@pure
def value() -> uint256:
    return 42
"""


def test_pure_function_needs_no_lock_slot(get_contract):
    # The compiler emits no nonreentrancy storage layout for this pure-only
    # contract. Loading and calling it must therefore succeed without a slot.
    assert get_contract(CONTRACT).value() == 42
