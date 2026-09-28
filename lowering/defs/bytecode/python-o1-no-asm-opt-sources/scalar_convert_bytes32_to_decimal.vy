# pragma enable-decimals

@external
@pure
def bytes32_to_decimal(x: bytes32) -> decimal:
    return convert(x, decimal)
