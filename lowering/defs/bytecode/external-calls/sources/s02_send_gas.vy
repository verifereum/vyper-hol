# send with gas=
@external
def f(t: address, v: uint256, g: uint256):
    send(t, v, gas=g)
