# a17: for-loop over an immutable array inside __init__ (ctor element load)
A: immutable(uint256[3])
s: uint256

@deploy
def __init__():
    A = [1, 2, 3]
    for x: uint256 in A:
        self.s += x

@external
def get() -> uint256:
    return self.s
