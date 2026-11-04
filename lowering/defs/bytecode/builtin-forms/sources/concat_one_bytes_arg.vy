# concat of one Bytes arg and a bytes4 arg (single calldata Bytes copy)
@external
@pure
def f(a: Bytes[10], c: bytes4) -> Bytes[14]:
    return concat(a, c)
