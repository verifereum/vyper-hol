struct P:
    l: uint256
    r: uint256

p: P
x: uint256

@external
def f() -> (uint256, uint256):
    return self.x, self.p.r
