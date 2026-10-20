"""Finding 48: nested creation preserves the configured EVM chain ID."""

from pyrevm import BlockEnv, CfgEnv, EVM, Env

CHILD = """
saved_chain_id: public(uint256)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_chain_id = chain.id
    self.saved_timestamp = block.timestamp
"""

FACTORY = """
created: public(address)

@external
def create(blueprint: address):
    self.created = create_from_blueprint(blueprint)
"""

CHAIN_ID = 31337


def _set_chain_id(env):
    old = env._evm.env.block
    env._evm = EVM(
        gas_limit=env.gas_limit,
        tracing=False,
        spec_id="prague",
        env=Env(
            cfg=CfgEnv(chain_id=CHAIN_ID),
            block=BlockEnv(
                number=old.number,
                coinbase=old.coinbase,
                timestamp=old.timestamp,
                prevrandao=old.prevrandao,
                basefee=old.basefee,
                gas_limit=old.gas_limit,
                excess_blob_gas=old.excess_blob_gas,
            ),
        ),
    )
    for account in env.accounts:
        env.set_balance(account, 10**30)


def test_nested_create_preserves_chain_id(get_contract, deploy_blueprint_for, env):
    _set_chain_id(env)
    blueprint, Child = deploy_blueprint_for(CHILD)
    factory = get_contract(FACTORY)

    factory.create(blueprint.address)
    child = Child(factory.created())

    assert child.saved_chain_id() == CHAIN_ID
    assert child.saved_timestamp() == env.timestamp
