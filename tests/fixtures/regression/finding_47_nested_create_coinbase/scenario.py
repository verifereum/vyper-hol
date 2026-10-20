"""Finding 47: nested creation receives the caller's block coinbase context."""

from pyrevm import BlockEnv

CHILD = """
saved_coinbase: public(address)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_coinbase = block.coinbase
    self.saved_timestamp = block.timestamp
"""

FACTORY = """
created: public(address)

@external
def create(blueprint: address):
    self.created = create_from_blueprint(blueprint)
"""

COINBASE = "0x0000000000000000000000000000000000001234"


def _set_coinbase(env):
    old = env._evm.env.block
    env._evm.set_block_env(
        BlockEnv(
            number=old.number,
            coinbase=COINBASE,
            timestamp=old.timestamp,
            prevrandao=old.prevrandao,
            basefee=old.basefee,
            gas_limit=old.gas_limit,
            excess_blob_gas=old.excess_blob_gas,
        )
    )


def test_nested_create_preserves_block_context(get_contract, deploy_blueprint_for, env):
    blueprint, Child = deploy_blueprint_for(CHILD)
    factory = get_contract(FACTORY)
    _set_coinbase(env)

    factory.create(blueprint.address)
    child = Child(factory.created())

    assert child.saved_coinbase() == COINBASE
    assert child.saved_timestamp() == env.timestamp
