
@external
@pure
def unsigned_shift(item: uint256, amount: int256) -> uint256:
    return shift(item, amount)

@external
@pure
def signed_shift(item: int256, amount: int256) -> int256:
    return shift(item, amount)
