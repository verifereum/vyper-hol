owner: public(address)
slot: public(uint256)

@deploy
def __init__():
    self.owner = msg.sender
