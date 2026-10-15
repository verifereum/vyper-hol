@external
@pure
def recover(h: bytes32, v: uint256, r: uint256, s: uint256) -> address:
    return ecrecover(h, v, r, s)

@external
@pure
def add_points(p: uint256[2], q: uint256[2]) -> uint256[2]:
    return ecadd(p, q)

@external
@pure
def multiply_point(p: uint256[2], scalar: uint256) -> uint256[2]:
    return ecmul(p, scalar)
