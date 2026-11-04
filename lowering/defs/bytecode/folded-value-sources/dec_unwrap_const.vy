U: constant(bool) = False
@external
@pure
def f(d: Bytes[64]) -> (uint256, bool):
    return abi_decode(d, (uint256, bool), unwrap_tuple=U)
