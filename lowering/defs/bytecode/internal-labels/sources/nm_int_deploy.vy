# internal function named __deploy (deploy unit entry label), called from the constructor
x: uint256

@internal
def __deploy(y: uint256) -> uint256:
    return y + 1

@deploy
def __init__():
    self.x = self.__deploy(5)

@external
def get() -> uint256:
    return self.x
