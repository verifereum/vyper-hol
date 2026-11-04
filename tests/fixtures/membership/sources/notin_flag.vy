flag F:
    A
    B
@external
def f(x: F) -> bool:
    return x not in (F.A | F.B)
