import ownable
initializes: ownable

supply: public(uint256)

@deploy
def __init__():
    ownable.__init__()

@internal
def _mint(amount: uint256):
    ownable._check_owner()
    self.supply += amount
