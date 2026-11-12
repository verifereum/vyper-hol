# diamond: two internals both calling a shared internal
@internal
def h(y: uint256) -> uint256:
    return y + 1

@internal
def f(y: uint256) -> uint256:
    return self.h(y)

@internal
def g(y: uint256) -> uint256:
    return self.h(y)

@external
def foo(x: uint256) -> uint256:
    a: uint256 = self.f(x)
    return self.g(a)
