struct T:
    a: uint256
    b: int256
    c: bytes32

t: T

@external
def f(x: bytes32) -> bytes32:
    self.t.c = x
    return self.t.c
