"""Finding 14: send propagates a recipient revert and rolls back value."""

SENDER = """
@external
def pay(recipient: address) -> uint256:
    send(recipient, 1)
    return 7
"""

RECEIVER = """
@external
@payable
def __default__():
    raise
"""


def test_send_to_reverting_contract_reverts(get_contract, env, tx_failed):
    sender = get_contract(SENDER)
    receiver = get_contract(RECEIVER)
    env.set_balance(sender.address, 10)

    with tx_failed():
        sender.pay(receiver.address)

    assert env.get_balance(sender.address) == 10
    assert env.get_balance(receiver.address) == 0
