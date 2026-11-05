# a10-11: hash the literal at compile time.
@external
def f(a: String[3]) -> bool:
    return a == "abc"
