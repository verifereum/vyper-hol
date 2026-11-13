A: immutable(uint256)
B: immutable(uint256)
C: immutable(uint256)

@deploy
def __init__():
    A = 1
    B = 2
    C = 3

@external
def f() -> uint256:
    return A + B + C
