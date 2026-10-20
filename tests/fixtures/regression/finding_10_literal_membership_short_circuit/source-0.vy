
@external
@pure
def contains(divisor: uint256) -> bool:
    return 1 in [1, 1 // divisor]
