# control (no a08 builtin): abi_encode with method_id returned
@external
def foo(x: uint256) -> Bytes[36]:
    return abi_encode(x, method_id=method_id("f(uint256)"))
