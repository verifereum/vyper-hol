# abi_encode result assigned to a local of larger Bytes type, then len()
@external
@pure
def f(a: int128, b: bool) -> uint256:
    v: (int128, bool) = (a, b)
    r: Bytes[100] = abi_encode(v, ensure_tuple=False, method_id=0xdeadbeef)
    return len(r)
