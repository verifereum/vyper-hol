# raw_create with ctor args and salt and value
@external
@payable
def foo(b: Bytes[100], x: uint256, s: bytes32) -> address:
    return raw_create(b, x, salt=s, value=msg.value)
