# abi_decode to tuple (uint256, DynArray[uint256,2]) with unwrap_tuple=False
@external
@pure
def f(d: Bytes[160]) -> uint256:
    t: (uint256, DynArray[uint256, 2]) = abi_decode(d, (uint256, DynArray[uint256, 2]), unwrap_tuple=False)
    return t[0]
