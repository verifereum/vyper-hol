"""Finding 6: augmented assignment snapshots the old LHS before its RHS."""

CONTRACT = """
stored: uint256

@internal
def overwrite_and_return_one() -> uint256:
    self.stored = 100
    return 1

@external
def run() -> uint256:
    self.stored = 10

    # The addition uses the old value 10. The RHS changes storage to 100,
    # but the final assignment stores the previously computed 10 + 1.
    self.stored += self.overwrite_and_return_one()
    return self.stored
"""


def test_old_left_hand_value_is_captured_before_rhs_effects(get_contract):
    contract = get_contract(CONTRACT)
    assert contract.run() == 11
