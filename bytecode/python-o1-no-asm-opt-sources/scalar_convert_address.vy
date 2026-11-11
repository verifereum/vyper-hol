@external
@pure
def address_to_uint(x: address) -> uint256:
    return convert(x, uint256)

@external
@pure
def uint_to_address(x: uint256) -> address:
    return convert(x, address)
