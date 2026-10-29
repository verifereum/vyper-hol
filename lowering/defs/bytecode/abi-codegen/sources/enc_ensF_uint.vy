# abi_encode of a single uint256, ensure_tuple=False, no method_id
@external
@pure
def f(a: uint256) -> Bytes[32]:
    return abi_encode(a, ensure_tuple=False)
