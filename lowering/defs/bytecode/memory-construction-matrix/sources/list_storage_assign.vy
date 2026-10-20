# list literal assigned to storage array
a: uint256[3]
@external
def f(x: uint256):
    self.a = [x, 2, 3]
