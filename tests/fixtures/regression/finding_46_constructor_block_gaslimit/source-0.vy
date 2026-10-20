
saved_gaslimit: public(uint256)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_gaslimit = block.gaslimit
    self.saved_timestamp = block.timestamp
