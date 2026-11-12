# a11: Assign of empty(String[5]) to a String local (zero-length fast path)
@external
def f() -> String[5]:
    s: String[5] = "abc"
    s = empty(String[5])
    return s
