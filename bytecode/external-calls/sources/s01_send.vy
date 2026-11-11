# send without gas=
@external
def f(t: address, v: uint256):
    send(t, v)
