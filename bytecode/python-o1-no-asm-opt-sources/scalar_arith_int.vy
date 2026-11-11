@external
@pure
def add_i256(a: int256, b: int256) -> int256:
    return a + b

@external
@pure
def sub_i256(a: int256, b: int256) -> int256:
    return a - b

@external
@pure
def mul_i256(a: int256, b: int256) -> int256:
    return a * b

@external
@pure
def div_i256(a: int256, b: int256) -> int256:
    return a // b

@external
@pure
def mod_i256(a: int256, b: int256) -> int256:
    return a % b
