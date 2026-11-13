# S names T before T is declared; T must still be sized as two words.
struct S:
    a: uint256
    t: T
struct T:
    p: uint256
    q: bool
@external
@pure
def f(a: uint256) -> S:
    return S(a=a, t=T(p=a, q=True))
