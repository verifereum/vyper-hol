# Regression control: a string with method_id, no tuple staging.
@external
@pure
def f(x: String[40]) -> Bytes[100]:
    return abi_encode(x, ensure_tuple=False, method_id=0xdeadbeef)
