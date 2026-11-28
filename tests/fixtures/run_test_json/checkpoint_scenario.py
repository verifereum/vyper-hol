"""Run through the external fuzzing runner to capture and compare full state.

This is a reference-execution scenario, not a second checkpoint producer.
The external runner supplies the pinned upstream fixtures and snapshot hooks.
"""

import pytest

from tests.evm_backends.base_env import EvmError

SOURCE = '''event Changed:
    value: uint256

stored: uint256
scratch: transient(uint256)

@deploy
def __init__():
    self.stored = 3

@external
def update(x: uint256):
    self.stored = x
    self.scratch = x + 1
    log Changed(value=x)
'''


def test_source_state(get_contract):
    contract = get_contract(SOURCE)
    contract.update(9)


@pytest.mark.parametrize('self_call', [False, True])
def test_eoa_message(env, self_call):
    env.set_balance(env.deployer, 100)
    target = env.deployer if self_call else env.accounts[1]
    assert env.message_call(target, value=7) == b''
    assert env.get_balance(env.deployer) == (100 if self_call else 93)
    if not self_call:
        assert env.get_balance(target) == 7


def test_insufficient_message(env, tx_failed):
    env.set_balance(env.deployer, 1)
    with tx_failed(exception=EvmError):
        env.message_call(env.accounts[1], value=2)
    assert env.get_balance(env.deployer) == 1


def test_raw_fallback(env):
    env.set_balance(env.deployer, 100)
    runtime = bytes.fromhex('6001600055600260015d602a600052600160206000a100')
    initcode = bytes([0x60, len(runtime), 0x60, 12, 0x60, 0, 0x39,
                      0x60, len(runtime), 0x60, 0, 0xf3]) + runtime
    contract = env.deploy([], initcode)
    assert env.message_call(contract.address) == b''
