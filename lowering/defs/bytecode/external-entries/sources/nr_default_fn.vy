# @nonreentrant on __default__
x: uint256

@external
@payable
@nonreentrant
def __default__():
    self.x = msg.value
