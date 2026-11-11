# a11: Assign [] to a storage DynArray (zero-length fast path, storage)
d: DynArray[uint256, 3]

@external
def f():
    self.d = []
