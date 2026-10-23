# a10: ternary of String type
@external
def f(c: bool, a: String[10], b: String[10]) -> String[10]:
    return a if c else b
