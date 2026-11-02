x: uint256

@external
@payable
@nonreentrant
def __default__():
    if msg.value > 0:
        return
    self.x = 1
