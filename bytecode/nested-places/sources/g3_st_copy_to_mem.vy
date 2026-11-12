struct P:
    l: uint256
    r: uint256

p: P

@external
def f() -> uint256:
    m: P = self.p
    return m.r
