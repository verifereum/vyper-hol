error Many:
    xs: DynArray[uint256, 4]

@external
def fail(xs: DynArray[uint256, 4]):
    raise Many(xs)
