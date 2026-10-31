# a10-02: three variable comparisons, then left-folded complemented AND.
@external
def f(x: uint256, a: uint256, b: uint256, c: uint256) -> bool:
    return x not in [a, b, c]
