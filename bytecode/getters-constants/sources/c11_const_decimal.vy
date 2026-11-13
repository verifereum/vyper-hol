# pragma enable-decimals
C: constant(decimal) = 1.25

@external
def f() -> decimal:
    return C
