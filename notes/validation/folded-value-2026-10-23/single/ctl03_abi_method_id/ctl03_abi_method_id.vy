@external
def foo(x: uint256) -> Bytes[36]:
    return abi_encode(x, method_id=method_id("f(uint256)"))
