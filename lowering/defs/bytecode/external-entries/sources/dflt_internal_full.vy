# internal function with a default arg; caller passes it
@internal
def g(a: uint256, b: uint256 = 3) -> uint256:
    return a * b

@external
def f(a: uint256) -> uint256:
    return self.g(a, 5)
