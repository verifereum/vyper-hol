# slice of bytes32 source
@external
@pure
def f(a: bytes32) -> Bytes[10]:
    return slice(a, 3, 10)
