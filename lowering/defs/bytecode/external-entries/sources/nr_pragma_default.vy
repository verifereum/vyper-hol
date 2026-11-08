# nonreentrancy-by-default pragma with __default__
#pragma nonreentrancy on
x: uint256

@external
@payable
def __default__():
    self.x = msg.value
