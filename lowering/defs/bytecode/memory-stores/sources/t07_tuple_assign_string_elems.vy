# a11: tuple assignment with a String component
@internal
def g() -> (uint256, String[10]):
    return 1, "ab"

@external
def f() -> String[10]:
    a: uint256 = 0
    s: String[10] = ""
    a, s = self.g()
    return s
