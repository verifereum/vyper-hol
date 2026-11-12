# internal String return used inside a builtin (len)
@internal
def f(s: String[10]) -> String[10]:
    return s

@external
def foo(s: String[10]) -> uint256:
    return len(self.f(s))
