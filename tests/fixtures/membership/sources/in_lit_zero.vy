# a10: `in` on a static literal list containing the default value 0 (semantics sparse-array check)
@external
def f(x: uint256) -> bool:
    return x in [0, 1]
