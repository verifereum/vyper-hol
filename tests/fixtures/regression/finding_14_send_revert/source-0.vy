
@external
def pay(recipient: address) -> uint256:
    send(recipient, 1)
    return 7
