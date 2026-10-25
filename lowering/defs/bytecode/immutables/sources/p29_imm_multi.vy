# multiple immutables of word types
A: immutable(uint256)
B: immutable(address)
C: immutable(bytes32)

@deploy
def __init__(a: uint256):
    A = a
    B = msg.sender
    C = keccak256("x")

@external
def get() -> uint256:
    return A

@external
def who() -> address:
    return B

@external
def h() -> bytes32:
    return C
