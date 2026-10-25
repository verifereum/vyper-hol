# a17: DynArray immutable indexed at runtime with a constant index (length DLOAD for the bounds check)
D: immutable(DynArray[uint256, 3])

@deploy
def __init__():
    D = [7, 8]

@external
def get() -> uint256:
    return D[1]
