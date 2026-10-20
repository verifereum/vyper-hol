# (cross-area control for a06-08) append on a dynarray field of a local struct
struct S:
    a: uint256
    items: DynArray[uint256, 3]

@external
def f(x: uint256) -> uint256:
    s: S = S(a=x, items=[1])
    s.items.append(x)
    return s.items[1]
