# pop on a dynarray field (second field) of a local struct
struct S:
    a: uint256
    items: DynArray[uint256, 3]

@external
def f(x: uint256) -> uint256:
    s: S = S(a=x, items=[1, 2, 3])
    return s.items.pop()
