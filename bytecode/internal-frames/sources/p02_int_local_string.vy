# internal function with a String local (AnnAssign of non-word type)
@internal
def bar(s: String[10]) -> String[10]:
    t: String[10] = s
    return t

@external
def foo(s: String[10]) -> String[10]:
    return self.bar(s)
