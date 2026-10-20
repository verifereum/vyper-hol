
saved: public(bytes32)

@external
def capture():
    self.saved = block.prevhash
