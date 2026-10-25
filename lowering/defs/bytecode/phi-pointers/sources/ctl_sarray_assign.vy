# a10 control: static-array local from a parameter (no ternary)
@external
def f(c: bool, a: uint256[2]) -> uint256:
    x: uint256[2] = a
    return x[1]
