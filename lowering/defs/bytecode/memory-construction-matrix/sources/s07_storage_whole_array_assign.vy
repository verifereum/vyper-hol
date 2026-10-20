# a11: whole fixed storage array assigned from a literal
arr: uint256[3]

@external
def f(x: uint256):
    self.arr = [x, 2, 3]
