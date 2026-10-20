# a11: whole storage struct assigned from a struct literal
struct S:
    a: uint256
    b: uint256

st: S

@external
def f(x: uint256):
    self.st = S(a=x, b=2)
