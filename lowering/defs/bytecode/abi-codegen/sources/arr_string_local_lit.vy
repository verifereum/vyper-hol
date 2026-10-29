# local dynamic array of String literal returned
@external
@pure
def f(s: String[4]) -> DynArray[String[4], 2]:
    x: DynArray[String[4], 2] = [s, "ab"]
    return x
