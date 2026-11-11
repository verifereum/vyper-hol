# return-buffer order: internal returns String[20] (memory return), argument is a String concat
@internal
def f(s: String[20]) -> String[20]:
    return s

@external
def foo(s: String[10]) -> String[20]:
    return self.f(concat(s, s))
