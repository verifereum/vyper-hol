# control for d05: the same calls with every argument supplied
@internal
def g(x: uint256 = 2) -> uint256:
    return x + 1

@internal
def f(x: uint256, y: uint256 = 4) -> uint256:
    return x * y

@external
def nested() -> uint256:
    return self.f(self.g(2), 4)
