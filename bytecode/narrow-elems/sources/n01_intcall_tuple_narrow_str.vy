# a tuple literal argument with a narrower String element
@internal
def f(t: (String[10], uint256)) -> uint256:
    return t[1]

@external
def a() -> uint256:
    s: String[5] = "hello"
    return 1 + self.f((s, 1))
