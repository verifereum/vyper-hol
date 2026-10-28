owner: public(address)

@deploy
def __init__():
    self.owner = msg.sender

@internal
@view
def _check():
    assert msg.sender == self.owner
