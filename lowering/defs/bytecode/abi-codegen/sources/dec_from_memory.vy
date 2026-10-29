# abi_decode of a memory local (not calldata) to (uint256, address)
@external
@pure
def f(a: uint256) -> address:
    d: Bytes[64] = abi_encode(a, a)
    t: (uint256, address) = abi_decode(d, (uint256, address), unwrap_tuple=False)
    return t[1]
