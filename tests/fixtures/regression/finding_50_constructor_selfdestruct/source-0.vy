
@deploy
def __init__():
    selfdestruct(msg.sender)

@external
@view
def marker() -> uint256:
    return 7
