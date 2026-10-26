# Regression control: a uint256 with method_id, no tuple staging.
@external
@pure
def f(x: uint256) -> Bytes[36]:
    return abi_encode(x, ensure_tuple=False, method_id=0xdeadbeef)
