x: uint256

@internal
@nonreentrant
def g(a: uint256):
    if a > 0:
        return
    self.x = 1

@external
def f(a: uint256):
    self.g(a)
    self.g(a)
