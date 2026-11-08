# a11: tuple assignment a, b = self.g()
@internal
def g() -> (uint256, uint256):
    return 1, 2

@external
def f() -> uint256:
    a: uint256 = 0
    b: uint256 = 0
    a, b = self.g()
    return a * 10 + b
