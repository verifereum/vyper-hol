# nonreentrant internal view function
x: uint256

@internal
@view
@nonreentrant
def g() -> uint256:
    return self.x

@external
def f() -> uint256:
    return self.g()
