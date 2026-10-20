# dynamic array literal of bytes20 local
@external
@pure
def f(a: bytes20) -> DynArray[bytes20, 2]:
    x: DynArray[bytes20, 2] = [a]
    return x
