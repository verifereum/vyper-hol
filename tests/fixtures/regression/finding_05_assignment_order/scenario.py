"""Finding 5: ordinary assignment evaluates the RHS before its target."""

CONTRACT = """
@external
def run() -> uint256[2]:
    indices: DynArray[uint256, 2] = [0, 1]
    result: uint256[2] = [7, 8]

    # RHS indices.pop() returns 1 and leaves [0]. Resolving the target next
    # pops 0, so the assignment is result[0] = 1.
    result[indices.pop()] = indices.pop()
    return result
"""


def test_rhs_side_effect_happens_before_target_side_effect(get_contract):
    contract = get_contract(CONTRACT)
    assert contract.run() == [1, 8]
