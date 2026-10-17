# cross-area check: assign abi_encode result into a Bytes local of the exact same bound
@external
@pure
def f(a: int128, b: bool) -> uint256:
    v: (int128, bool) = (a, b)
    r: Bytes[68] = abi_encode(v, ensure_tuple=False, method_id=0xdeadbeef)
    return len(r)
