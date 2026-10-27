# a range-loop variable and an accumulator local in a constructor
x: uint256

@deploy
def __init__():
    acc: uint256 = 0
    for i: uint256 in range(4):
        acc += i
    self.x = acc

@external
def get() -> uint256:
    return self.x
