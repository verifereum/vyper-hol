"""Finding 40: block.gaslimit is independent of the call gas allowance."""

CONTRACT = """
@external
@view
def block_limit() -> uint256:
    return block.gaslimit

@external
@view
def number_control() -> uint256:
    return block.number
"""


def test_block_limit_does_not_change_with_call_allowance(get_contract, gas_limit):
    contract = get_contract(CONTRACT)

    assert contract.block_limit(gas=100_000) == gas_limit
    assert contract.block_limit(gas=200_000) == gas_limit
    assert contract.number_control(gas=100_000) == 1
    assert contract.number_control(gas=200_000) == 1
