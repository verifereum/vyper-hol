@external
@pure
def f(a: address) -> Bytes[36]:
    return abi_encode(a, method_id=0xdeadbeef)
