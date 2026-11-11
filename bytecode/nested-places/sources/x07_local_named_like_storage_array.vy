a: DynArray[uint256, 3]

@external
def f(i: uint256) -> uint256:
    a: uint256[2] = [5, 6]
    return a[i]
