struct P:
    a: uint256
    b: uint256

@internal
def f(y: uint256) -> P:
    p: P = P(a=y, b=y)
    p.b = 7
    return p

@external
def foo(x: uint256) -> uint256:
    return self.f(x).b
