# a10: x in calldata static array (argument)
@external
def f(x: uint256, a: uint256[3]) -> bool:
    return x in a
