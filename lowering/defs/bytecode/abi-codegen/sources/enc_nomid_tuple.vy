# abi_encode of a shallow scalar tuple, ensure_tuple=False, no method_id
@external
@pure
def f(a: int128, b: bool) -> Bytes[64]:
    v: (int128, bool) = (a, b)
    return abi_encode(v, ensure_tuple=False)
