# nested struct literal
struct T:
    p: uint256
    q: bool

struct S:
    a: uint256
    t: T

@external
@pure
def f(a: uint256) -> S:
    return S(a=a, t=T(p=a, q=True))
