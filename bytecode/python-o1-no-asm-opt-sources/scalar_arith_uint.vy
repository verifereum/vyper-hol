@external
@pure
def add_u256(a: uint256, b: uint256) -> uint256:
    return a + b

@external
@pure
def sub_u256(a: uint256, b: uint256) -> uint256:
    return a - b

@external
@pure
def mul_u256(a: uint256, b: uint256) -> uint256:
    return a * b

@external
@pure
def div_u256(a: uint256, b: uint256) -> uint256:
    return a // b

@external
@pure
def mod_u256(a: uint256, b: uint256) -> uint256:
    return a % b
