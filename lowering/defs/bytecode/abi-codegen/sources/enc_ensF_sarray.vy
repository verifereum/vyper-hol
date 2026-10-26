# Regression control: a fixed array, no tuple staging.
@external
@pure
def f(x: uint256[2]) -> Bytes[64]:
    return abi_encode(x, ensure_tuple=False)
