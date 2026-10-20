# pop on a dynarray field of a local struct, popped value discarded, then read length
struct S:
    items: DynArray[uint256, 3]
    a: uint256

@external
def f(x: uint256) -> uint256:
    s: S = S(items=[1, 2, x], a=7)
    s.items.pop()
    return len(s.items)
