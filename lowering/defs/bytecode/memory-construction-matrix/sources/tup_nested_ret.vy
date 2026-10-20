# nested tuple return value
@external
@pure
def f(a: uint256) -> (uint256, (uint256, bool)):
    return a, (a, True)
