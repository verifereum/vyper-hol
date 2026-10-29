# subscript of a dynamic array of String returning String
@external
@pure
def f(x: DynArray[String[10], 3], i: uint256) -> String[10]:
    return x[i]
