@external
def f(a: uint256, b: bool = True, c: address = empty(address)) -> uint256:
    if b and c == empty(address):
        return a
    return 0
