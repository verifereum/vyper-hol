# internal function performing an external staticcall
interface I:
    def bar(x: uint256) -> uint256: view

@internal
@view
def f(t: address, y: uint256) -> uint256:
    return staticcall I(t).bar(y)

@external
@view
def foo(t: address, x: uint256) -> uint256:
    return self.f(t, x)
