# a11: assign a string literal to a String local after declaration
@external
def f() -> String[10]:
    s: String[10] = "a"
    s = "abc"
    return s
