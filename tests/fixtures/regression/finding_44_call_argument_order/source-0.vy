
received: public(uint256)

@external
@payable
def accept(item: uint256):
    self.received = item
