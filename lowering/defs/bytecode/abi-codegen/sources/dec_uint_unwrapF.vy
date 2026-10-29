# abi_decode to uint256 with unwrap_tuple=False
@external
@pure
def f(d: Bytes[32]) -> uint256:
    return abi_decode(d, uint256, unwrap_tuple=False)
