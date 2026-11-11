# raw_call with data built by abi_encode with method_id
@external
def foo(t: address, x: uint256):
    raw_call(t, abi_encode(x, method_id=method_id("f(uint256)")))
