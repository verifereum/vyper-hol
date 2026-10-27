import token
initializes: token

owner: public(address)

@deploy
def __init__():
    token.__init__()
    self.owner = msg.sender

@external
def mint(amount: uint256):
    token._mint(amount)
