# nested tuple local (AnnAssign) returned
@external
@pure
def f(a: uint256) -> (uint256, (uint256, bool)):
    x: (uint256, (uint256, bool)) = (a, (a, False))
    return x
