# a10 control: String result selected through if/else statements instead of a ternary
@external
def f(c: bool, a: String[10], b: String[10]) -> String[10]:
    if c:
        return a
    return b
