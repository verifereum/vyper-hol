"""Finding 53: send(self, amount) still checks the sender's available balance."""

CONTRACT = """
marker: public(uint256)

@external
def transfer_to_self(amount: uint256):
    send(self, amount)
    self.marker = 1
"""


def test_self_send_checks_available_balance(get_contract, tx_failed, env):
    contract = get_contract(CONTRACT)
    assert env.get_balance(contract.address) == 0

    with tx_failed():
        contract.transfer_to_self(1)
    assert contract.marker() == 0
