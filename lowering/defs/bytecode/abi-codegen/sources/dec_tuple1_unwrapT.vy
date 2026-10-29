# abi_decode to single-element tuple (uint256,) with unwrap_tuple=True
@external
@pure
def f(d: Bytes[32]) -> uint256:
    t: (uint256,) = abi_decode(d, (uint256,))
    return t[0]
