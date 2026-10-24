# a10: ternary of struct type
struct S:
    a: uint256
    b: address
@external
def f(c: bool, x: uint256) -> uint256:
    s: S = S(a=x, b=msg.sender) if c else S(a=1, b=self)
    return s.a
