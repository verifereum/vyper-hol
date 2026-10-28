import token

initializes: token
initializes: token.ownable

owner: public(address)

@deploy
def __init__():
    token.ownable.__init__()
    self.owner = msg.sender
