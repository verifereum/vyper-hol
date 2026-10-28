# a10: ternary of static-array type assigned to a local
@external
def f(c: bool, a: uint256[2]) -> uint256:
    x: uint256[2] = a if c else [1, 2]
    return x[1]
