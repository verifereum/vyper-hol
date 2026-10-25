# a10: `in` on a local static array containing default elements
@external
def f(x: uint256, y: uint256) -> bool:
    a: uint256[3] = [y, 0, 5]
    return x in a
