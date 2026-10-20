
saved_coinbase: public(address)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_coinbase = block.coinbase
    self.saved_timestamp = block.timestamp
