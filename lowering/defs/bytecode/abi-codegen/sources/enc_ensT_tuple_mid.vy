# abi_encode of a shallow scalar tuple, ensure_tuple=True (default), with method_id
@external
@pure
def f(a: int128, b: bool) -> Bytes[68]:
    v: (int128, bool) = (a, b)
    return abi_encode(v, method_id=0xdeadbeef)
