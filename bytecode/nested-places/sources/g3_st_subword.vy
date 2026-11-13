struct S:
    a: uint8
    b: address
    c: bool

s: S

@external
def f(x: address) -> address:
    self.s.b = x
    self.s.a = 3
    return self.s.b
