# empty(uint256[2]) as log arg after memory at 0 was dirtied (miscompile witness)
event E:
    a: uint256[2]

@external
def f(x: uint256):
    log E(a=[x, x])
    log E(a=empty(uint256[2]))
