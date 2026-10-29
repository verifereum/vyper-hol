# Regression control: a word-element dynamic array, no tuple staging.
@external
@pure
def f(x: DynArray[uint256, 3]) -> Bytes[128]:
    return abi_encode(x, ensure_tuple=False)
