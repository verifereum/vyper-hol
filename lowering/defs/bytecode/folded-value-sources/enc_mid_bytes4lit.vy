@external
@pure
def f(a: int128, b: bool) -> Bytes[68]:
    v: (int128, bool) = (a, b)
    return abi_encode(v, ensure_tuple=False, method_id=b"\xde\xad\xbe\xef")
