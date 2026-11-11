# SEQ-354 c1: a tuple literal argument with a narrower String element
@internal
def f(t: (String[10], uint256)) -> uint256:
    return t[1]

@external
def a(s: String[5]) -> uint256:
    return 1 + self.f((s, 1))
