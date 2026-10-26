# list literal of Bytes (non-word elements)
@external
@pure
def f(a: Bytes[4]) -> DynArray[Bytes[4], 2]:
    return [a, b"ab"]
