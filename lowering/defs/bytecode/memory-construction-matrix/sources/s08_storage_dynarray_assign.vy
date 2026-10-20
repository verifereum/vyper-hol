# a11: whole storage DynArray assigned from a literal
d: DynArray[uint256, 4]

@external
def f(x: uint256):
    self.d = [x, 2]
