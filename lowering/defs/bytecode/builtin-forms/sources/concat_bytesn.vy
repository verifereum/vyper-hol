# concat of bytes32 and bytes4 and Bytes
@external
@pure
def f(a: bytes32, b: bytes4, c: Bytes[8]) -> Bytes[44]:
    return concat(a, b, c)
