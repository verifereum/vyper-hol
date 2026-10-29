# abi_decode to (uint256, bool) with default unwrap_tuple=True (no wrap: len>1)
@external
@pure
def f(d: Bytes[64]) -> (uint256, bool):
    return abi_decode(d, (uint256, bool))
