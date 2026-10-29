# for loop over a dynamic array of String
@external
@pure
def f(x: DynArray[String[10], 3]) -> uint256:
    n: uint256 = 0
    for s: String[10] in x:
        n += len(s)
    return n
