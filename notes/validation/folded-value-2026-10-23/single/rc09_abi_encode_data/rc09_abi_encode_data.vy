@external
def foo(t: address, x: uint256):
    raw_call(t, abi_encode(x, method_id=method_id("f(uint256)")))
