# String local AnnAssign initialised by an internal call (supported root)
@internal
def f(s: String[10]) -> String[10]:
    return s

@external
def foo(s: String[10]) -> String[10]:
    t: String[10] = self.f(s)
    return t
