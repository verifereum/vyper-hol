@external
@pure
def shift_left(a: uint256, b: uint256) -> uint256:
    return a << b

@external
@pure
def shift_right_unsigned(a: uint256, b: uint256) -> uint256:
    return a >> b

@external
@pure
def shift_right_signed(a: int256, b: uint256) -> int256:
    return a >> b
