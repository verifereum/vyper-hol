# internal function with a struct local
struct P:
    a: uint256
    b: uint256

@internal
def bar(y: uint256) -> uint256:
    p: P = P(a=y, b=2)
    return p.b + p.a

@external
def foo(x: uint256) -> uint256:
    return self.bar(x)
