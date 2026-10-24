# control for rr_local: concat local returned without raw_return
@external
def f(a: Bytes[10]) -> Bytes[40]:
    b: Bytes[40] = concat(a, a)
    return b
