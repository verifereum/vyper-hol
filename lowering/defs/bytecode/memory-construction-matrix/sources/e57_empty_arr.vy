# empty(...) builtin as array log arg
event E:
    a: uint256[2]

@external
def f():
    log E(a=empty(uint256[2]))
