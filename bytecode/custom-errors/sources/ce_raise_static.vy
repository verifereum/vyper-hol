error Bad:
    code: uint256
    who: address
    tag: bytes32

@external
def fail(c: uint256, t: bytes32):
    raise Bad(c, msg.sender, t)
