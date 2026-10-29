# nonreentrancy-by-default pragma with a constructor (deploy is not external)
#pragma nonreentrancy on
x: uint256

@deploy
def __init__():
    self.x = 1

@external
def f() -> uint256:
    return self.x
