@external
@pure
def logical_not(a: bool) -> bool:
    return not a

@external
@pure
def bitwise_not(a: uint256) -> uint256:
    return ~a

@external
@pure
def negate(a: int256) -> int256:
    return -a

@external
@pure
def absolute(a: int256) -> int256:
    return abs(a)
