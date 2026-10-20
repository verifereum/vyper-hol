
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
