"""Finding 46: constructors observe the block gas limit from their environment."""

CONTRACT = """
saved_gaslimit: public(uint256)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_gaslimit = block.gaslimit
    self.saved_timestamp = block.timestamp
"""


def test_constructor_observes_block_gaslimit(get_contract, env):
    contract = get_contract(CONTRACT)

    assert contract.saved_gaslimit() == env.gas_limit
    assert contract.saved_timestamp() == env.timestamp
