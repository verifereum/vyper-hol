
saved_randomness: public(bytes32)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_randomness = block.prevrandao
    self.saved_timestamp = block.timestamp
