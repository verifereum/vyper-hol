"""Finding 9: fixed-array membership includes implicit default elements."""

CONTRACT = """
@external
@pure
def zero_is_present_in_empty_array() -> bool:
    values: uint256[2] = empty(uint256[2])
    return 0 in values

@external
@pure
def zero_is_absent_from_empty_array() -> bool:
    values: uint256[2] = empty(uint256[2])
    return 0 not in values

@external
@pure
def contains(item: uint256) -> bool:
    values: uint256[2] = [0, 7]
    return item in values
"""


def test_membership_searches_implicit_and_explicit_elements(get_contract):
    contract = get_contract(CONTRACT)

    assert contract.zero_is_present_in_empty_array() is True
    assert contract.zero_is_absent_from_empty_array() is False
    assert contract.contains(0) is True
    assert contract.contains(7) is True
    assert contract.contains(9) is False
