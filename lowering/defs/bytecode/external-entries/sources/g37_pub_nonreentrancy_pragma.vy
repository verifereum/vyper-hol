# pragma nonreentrancy on
# a01: public getter under nonreentrancy-by-default pragma (getter must check the lock)
g: public(uint256)

@external
def set(x: uint256):
    self.g = x
