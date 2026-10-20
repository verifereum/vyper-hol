
marker: public(uint256)

@external
def transfer_to_self(amount: uint256):
    send(self, amount)
    self.marker = 1
