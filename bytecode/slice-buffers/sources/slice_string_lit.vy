# slice of String arg with literal start/len
@external
@pure
def f(a: String[40]) -> String[5]:
    return slice(a, 2, 5)
