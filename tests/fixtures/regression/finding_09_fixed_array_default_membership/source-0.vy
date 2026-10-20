
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
