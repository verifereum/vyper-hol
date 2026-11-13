error Bad:
    code: uint256
    who: address

@external
def check(x: uint256):
    assert x < 10, Bad(x, msg.sender)
