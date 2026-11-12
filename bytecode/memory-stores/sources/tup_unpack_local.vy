# tuple unpacking assignment from a tuple local
@external
@pure
def f(a: uint256, b: bool) -> uint256:
    x: (uint256, bool) = (a, b)
    c: uint256 = 0
    d: bool = False
    c, d = x
    return c
