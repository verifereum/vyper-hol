# a11: memory target d[i] = x on a local DynArray
@external
def f(i: uint256, x: uint256) -> uint256:
    d: DynArray[uint256, 3] = [1, 2, 3]
    d[i] = x
    return d[2]
