# a11: control for s07: whole storage array from literal using arg x, with x still live afterwards
arr: uint256[3]
y: uint256

@external
def f(x: uint256):
    self.arr = [x, 2, 3]
    self.y = x
