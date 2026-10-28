struct P:
    x: uint256
    y: uint256

x: uint256
p: P

@external
def f(a: uint256) -> uint256:
    self.p.x = a
    return self.p.x
