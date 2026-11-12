# a10: ternary of flag type
flag F:
    A
    B
@external
def f(c: bool) -> F:
    return F.A if c else F.B
