@external
@payable
def forward_value(recipient: address, amount: uint256):
    send(recipient, amount)
