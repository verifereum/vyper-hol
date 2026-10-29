# Regression control: single signed scalar, no tuple staging.
@external
@pure
def f(x: int8) -> Bytes[32]:
    return abi_encode(x, ensure_tuple=False)
