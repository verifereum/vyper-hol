# a17: DynArray immutable indexed inside __init__ (ctor length load_word + element load)
D: immutable(DynArray[uint256, 3])
x: uint256

@deploy
def __init__():
    D = [7, 8]
    self.x = D[1]

@external
def get() -> uint256:
    return self.x
