# DynArray immutable
D: immutable(DynArray[uint256, 3])

@deploy
def __init__():
    D = [1, 2]

@external
def get() -> uint256:
    return len(D)
