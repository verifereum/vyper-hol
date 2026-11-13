struct S:
    k: uint256
    d: DynArray[uint256, 3]

s: S

@external
def f(x: uint256) -> uint256:
    self.s.d.append(x)
    return self.s.d[0]
