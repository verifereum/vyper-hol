# constructor body that declares locals: Python gives each its own alloca
x: uint256
y: uint256

@deploy
def __init__():
    a: uint256 = 7
    b: uint256 = a + 1
    self.x = a
    self.y = b

@external
def get() -> uint256:
    return self.x + self.y
