# DynArray literal assigned to storage DynArray
a: DynArray[uint256, 4]
@external
def f(x: uint256):
    self.a = [x, 2]
