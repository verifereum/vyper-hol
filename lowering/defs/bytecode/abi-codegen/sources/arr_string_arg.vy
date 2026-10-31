# dynamic array of String as argument (len)
@external
@pure
def f(x: DynArray[String[10], 3]) -> uint256:
    return len(x)
