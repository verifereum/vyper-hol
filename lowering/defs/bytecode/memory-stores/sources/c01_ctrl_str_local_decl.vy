# a11 control (supported): String local declared from a literal and returned
@external
def f() -> String[10]:
    s: String[10] = "abc"
    return s
