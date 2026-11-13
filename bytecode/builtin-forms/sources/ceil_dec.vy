# ceil of decimal arg
# pragma enable-decimals
@external
@pure
def f(x: decimal) -> int256:
    return ceil(x)
