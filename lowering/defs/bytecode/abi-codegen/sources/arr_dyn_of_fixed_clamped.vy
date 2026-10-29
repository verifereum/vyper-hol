# dynamic array of uint8[2] (elements need clamp) as argument only
@external
@pure
def f(x: DynArray[uint8[2], 3]) -> uint256:
    return len(x)
