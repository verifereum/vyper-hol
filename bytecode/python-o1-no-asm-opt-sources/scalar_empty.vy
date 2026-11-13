# pragma enable-decimals

@external
@pure
def empty_uint() -> uint256:
    return empty(uint256)

@external
@pure
def empty_bool() -> bool:
    return empty(bool)

@external
@pure
def empty_decimal() -> decimal:
    return empty(decimal)

@external
@pure
def empty_address() -> address:
    return empty(address)

@external
@pure
def get_empty_bytes32() -> bytes32:
    return empty(bytes32)
