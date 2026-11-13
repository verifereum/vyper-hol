# a11: assign an internal-call String result to a String local
@internal
def g() -> String[10]:
    return "xy"

@external
def f() -> String[10]:
    s: String[10] = ""
    s = self.g()
    return s
