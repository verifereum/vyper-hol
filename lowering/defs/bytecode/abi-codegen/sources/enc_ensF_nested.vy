# Regression control: a nested static tuple, no tuple staging.
@external
@pure
def f(x: ((uint256, bool), uint256)) -> Bytes[96]:
    return abi_encode(x, ensure_tuple=False)
