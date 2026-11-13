# abi_decode to uint256 with default unwrap_tuple=True
@external
@pure
def f(d: Bytes[32]) -> uint256:
    return abi_decode(d, uint256)
