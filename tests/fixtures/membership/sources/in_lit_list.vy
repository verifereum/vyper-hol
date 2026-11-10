# a10-02: emit all comparisons before left-folding membership.
@external
def f(x: uint256) -> bool:
    return x in [1, 2, 3]
