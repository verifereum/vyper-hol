# abi_decode to nested tuple ((uint256,bool),uint256) with unwrap_tuple=False
@external
@pure
def f(d: Bytes[96]) -> uint256:
    t: ((uint256, bool), uint256) = abi_decode(d, ((uint256, bool), uint256), unwrap_tuple=False)
    return t[1]
