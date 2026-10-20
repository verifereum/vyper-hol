@external
def f() -> String[5]:
    s: String[5] = "abc"
    s = empty(String[5])
    return s
