# abi_decode of a memory local Bytes (returned directly as tuple)
@external
@pure
def f(x: Bytes[64]) -> (uint256, address):
    d: Bytes[64] = x
    return abi_decode(d, (uint256, address), unwrap_tuple=False)
