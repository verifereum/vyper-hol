@external
@pure
def f(x: String[8]) -> bytes4:
    return convert(x, bytes4)
