# nested list literal uint256[2][2]
@external
@pure
def f(x: uint256) -> uint256[2][2]:
    return [[x, 1], [2, 3]]
