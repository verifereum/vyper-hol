"""Finding 41: the accepted shift() builtin is not an internal function call."""


CONTRACT = """
@external
@pure
def unsigned_shift(item: uint256, amount: int256) -> uint256:
    return shift(item, amount)

@external
@pure
def signed_shift(item: int256, amount: int256) -> int256:
    return shift(item, amount)
"""


def test_shift_builtin(get_contract):
    contract = get_contract(CONTRACT)
    assert contract.unsigned_shift(1, 8) == 256
    assert contract.unsigned_shift(256, -8) == 1
    assert contract.signed_shift(-256, -8) == -1
