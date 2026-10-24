# raw_revert with abi_encode data inside an if
@external
def foo(x: uint256):
    if x > 3:
        raw_revert(abi_encode(x, method_id=method_id("E(uint256)")))
