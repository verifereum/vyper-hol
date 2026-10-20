# flat word tuple literal whose element is a memory local (supported subset control)
@external
@pure
def f(a: uint256) -> (uint256, bool):
    x: uint256 = a
    return x, True
