event E:
    a: indexed(bytes20)
    b: bytes20

v: bytes20

@external
def f():
    log E(a=self.v, b=self.v)
