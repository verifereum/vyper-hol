"""Finding 15: a non-reverting raw call reports insufficient balance as False."""

CONTRACT = """
@external
def attempt(recipient: address, amount: uint256) -> bool:
    return raw_call(recipient, b"", value=amount, revert_on_failure=False)

@external
def attempt_with_data(recipient: address, amount: uint256) -> (bool, Bytes[4]):
    return raw_call(
        recipient,
        b"",
        value=amount,
        max_outsize=4,
        revert_on_failure=False,
    )
"""


def test_insufficient_balance_is_an_observed_call_failure(get_contract, env):
    contract = get_contract(CONTRACT)
    recipient = env.accounts[1]
    recipient_balance = env.get_balance(recipient)

    assert contract.attempt(recipient, 1) is False
    assert contract.attempt_with_data(recipient, 1) == (False, b"")
    assert env.get_balance(contract.address) == 0
    assert env.get_balance(recipient) == recipient_balance
