# DynArray literal of uint256 returned
@external
@pure
def f(x: uint256) -> DynArray[uint256, 4]:
    return [x, 2, 3]
