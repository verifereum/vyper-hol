# a01: DynArray immutable indexed at runtime
A: immutable(DynArray[uint256, 3])

@deploy
def __init__():
    A = [5, 6]

@external
def f(i: uint256) -> uint256:
    return A[i]
