
@external
@pure
def bit_and(left: bytes32, right: bytes32) -> bytes32:
    return left & right

@external
@pure
def bit_or(left: bytes32, right: bytes32) -> bytes32:
    return left | right

@external
@pure
def bit_xor(left: bytes32, right: bytes32) -> bytes32:
    return left ^ right

@external
@pure
def shift_left(item: bytes32, amount: uint256) -> bytes32:
    return item << amount

@external
@pure
def shift_right(item: bytes32, amount: uint256) -> bytes32:
    return item >> amount
