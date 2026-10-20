"""Finding 52: block.prevhash is zero at genesis instead of reverting."""

CONTRACT = """
saved: public(bytes32)

@external
def capture():
    self.saved = block.prevhash
"""


def test_genesis_prevhash_is_zero(get_contract, env):
    contract = get_contract(CONTRACT)
    env.block_number = 0

    contract.capture()
    assert contract.saved() == bytes(32)
