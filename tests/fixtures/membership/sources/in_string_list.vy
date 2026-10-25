# a10: String in list of Strings (non-word element membership)
@external
def f(x: String[5], a: String[5]) -> bool:
    return x in [a, "b"]
