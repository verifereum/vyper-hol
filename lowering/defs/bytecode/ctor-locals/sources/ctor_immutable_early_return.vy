marker: immutable(uint256)

@deploy
def __init__(early: bool):
    self.marker = 7
    if early:
        return

@external
@view
def answer() -> uint256:
    return self.marker
