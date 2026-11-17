#pragma enable-decimals
@external
def f(a: int256) -> decimal:
    return convert(a, decimal)
