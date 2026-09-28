@external
@pure
def add_mod(a: uint256, b: uint256, m: uint256) -> uint256:
    return uint256_addmod(a, b, m)

@external
@pure
def mul_mod(a: uint256, b: uint256, m: uint256) -> uint256:
    return uint256_mulmod(a, b, m)

@external
@pure
def power_mod_256(a: uint256, b: uint256) -> uint256:
    return pow_mod256(a, b)
