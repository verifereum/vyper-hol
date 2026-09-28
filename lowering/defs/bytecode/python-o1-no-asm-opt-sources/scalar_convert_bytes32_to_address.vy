@external
@pure
def bytes32_to_address(x: bytes32) -> address:
    return convert(x, address)
