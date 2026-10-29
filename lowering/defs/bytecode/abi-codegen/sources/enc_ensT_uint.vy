# abi_encode of a single uint256, default ensure_tuple=True, no method_id
@external
@pure
def f(a: uint256) -> Bytes[32]:
    return abi_encode(a)
