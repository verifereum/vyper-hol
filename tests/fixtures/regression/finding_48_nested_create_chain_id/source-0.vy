
saved_chain_id: public(uint256)
saved_timestamp: public(uint256)

@deploy
def __init__():
    self.saved_chain_id = chain.id
    self.saved_timestamp = block.timestamp
