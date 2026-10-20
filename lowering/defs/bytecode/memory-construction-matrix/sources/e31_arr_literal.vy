# fixed-array literal as log arg
event E:
    a: uint256[2]

@external
def f(x: uint256):
    log E(a=[x, 2])
