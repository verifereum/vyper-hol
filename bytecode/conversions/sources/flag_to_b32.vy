flag F:
    A
    B

@external
@pure
def f(x: F) -> bytes32:
    return convert(x, bytes32)
