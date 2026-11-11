error Unauthorized:
    caller: address
    amount: uint256

@external
def fail(a: uint256):
    raise Unauthorized(caller=msg.sender, amount=a)
