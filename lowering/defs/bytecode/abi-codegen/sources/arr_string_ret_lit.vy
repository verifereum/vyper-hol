# dynamic array of String returned from a calldata arg element copy (encode path, arg is a String)
@external
@pure
def f(s: String[10]) -> DynArray[String[10], 3]:
    x: DynArray[String[10], 3] = [s]
    return x
