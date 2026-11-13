struct S:
    k: uint256
    b: Bytes[40]

s: S

@external
def f() -> Bytes[40]:
    return self.s.b
