# a11: tuple assign inside a function whose return type differs from the RHS tuple type
@internal
def g() -> (uint256, uint256):
    return 1, 2

@external
def f() -> (String[5], uint256):
    a: uint256 = 0
    b: uint256 = 0
    a, b = self.g()
    return "x", a + b
