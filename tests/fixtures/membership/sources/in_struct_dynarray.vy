# a10: struct in DynArray of structs (non-word element membership)
struct S:
    a: uint256
@external
def f(a: DynArray[S, 3]) -> bool:
    return S(a=1) in a
