struct S:
    prefix: uint256
    items: DynArray[uint256[2], 3]

@external
def f(v: uint256[2]) -> S:
    s: S = S(prefix=17, items=[])
    s.items.append(v)
    return s
