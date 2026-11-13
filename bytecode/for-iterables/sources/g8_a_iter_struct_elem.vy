struct P:
    x: uint256
    y: uint256

a: P[2]

@external
def f() -> uint256:
    s: uint256 = 0
    for p: P in self.a:
        s += p.x + p.y
    return s
