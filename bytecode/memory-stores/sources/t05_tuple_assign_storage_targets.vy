# a11: tuple assignment to storage targets self.x, self.y = ...
x: uint256
y: uint256

@internal
def g() -> (uint256, uint256):
    return 1, 2

@external
def f():
    self.x, self.y = self.g()
