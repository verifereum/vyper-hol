"""Finding 49: nested creation preserves the block randomness context."""

from pyrevm import BlockEnv

CHILD = """
saved_randomness: public(bytes32)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_randomness = block.prevrandao
    self.saved_timestamp = block.timestamp
"""

FACTORY = """
created: public(address)

@external
def create(blueprint: address):
    self.created = create_from_blueprint(blueprint)
"""

RANDOMNESS = 0x1234


def _set_randomness(env):
    old = env._evm.env.block
    env._evm.set_block_env(
        BlockEnv(
            number=old.number,
            coinbase=old.coinbase,
            timestamp=old.timestamp,
            prevrandao=RANDOMNESS.to_bytes(32, "big"),
            basefee=old.basefee,
            gas_limit=old.gas_limit,
            excess_blob_gas=old.excess_blob_gas,
        )
    )


def test_nested_create_preserves_randomness(get_contract, deploy_blueprint_for, env):
    blueprint, Child = deploy_blueprint_for(CHILD)
    factory = get_contract(FACTORY)
    _set_randomness(env)

    factory.create(blueprint.address)
    child = Child(factory.created())

    assert child.saved_randomness() == RANDOMNESS.to_bytes(32, "big")
    assert child.saved_timestamp() == env.timestamp
