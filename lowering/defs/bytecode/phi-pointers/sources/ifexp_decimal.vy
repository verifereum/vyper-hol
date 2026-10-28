# a10: ternary of decimal (word, supported)
#pragma enable-decimals
@external
def f(c: bool, a: decimal) -> decimal:
    return a if c else 1.5
