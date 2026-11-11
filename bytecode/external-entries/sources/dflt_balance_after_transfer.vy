@external
@payable
def f(b: uint256 = msg.sender.balance) -> uint256:
    return b
