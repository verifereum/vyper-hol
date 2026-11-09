# a11: String local initialised from a String argument of the same type
@external
def f(s: String[10]) -> String[10]:
    t: String[10] = s
    return t
