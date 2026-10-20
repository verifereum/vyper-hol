"""Finding 45: top-level static traces reject state-changing source calls."""

from tests.evm_backends.base_env import EvmError


CONTRACT = """
stored: public(uint256)

@external
def set_value(item: uint256):
    self.stored = item
"""


def test_static_call_rejects_state_write(get_contract, env, tx_failed):
    contract = get_contract(CONTRACT)
    calldata = contract.set_value.prepare_calldata(7)

    with tx_failed(EvmError):
        env.message_call(
            contract.address,
            data=calldata,
            is_modifying=False,
            function_name="set_value",
            python_args={"args": [7], "kwargs": {}},
        )

    assert contract.stored() == 0
