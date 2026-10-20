
@external
@pure
def bool_to_decimal(item: bool) -> decimal:
    return convert(item, decimal)

@external
@pure
def bool_to_bytes(item: bool) -> bytes1:
    return convert(item, bytes1)

@external
@pure
def decimal_to_bool(item: decimal) -> bool:
    return convert(item, bool)

@external
@pure
def decimal_to_bytes(item: decimal) -> bytes21:
    return convert(item, bytes21)

@external
@pure
def string_to_bool(item: String[8]) -> bool:
    return convert(item, bool)
