# dynamic array literal of String literals returned directly
@external
@pure
def f() -> DynArray[String[4], 2]:
    return ["ab", "cde"]
