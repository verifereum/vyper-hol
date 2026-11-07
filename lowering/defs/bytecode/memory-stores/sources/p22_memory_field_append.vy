struct S:
    prefix: uint256
    items: DynArray[uint256, 4]

@external
def f(v: uint256) -> S:
    s: S = S(prefix=17, items=[3])
    s.items.append(v)
    return s
