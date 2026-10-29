# a10: x not in [literal list] with variable elements
@external
def f(x: uint256, a: uint256, b: uint256) -> bool:
    return x not in [a, b]
