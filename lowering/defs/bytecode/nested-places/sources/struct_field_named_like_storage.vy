struct P:
    x: uint256
    y: uint256

p: P
x: uint256

@external
def f() -> uint256:
    self.x = 7
    return self.p.x
