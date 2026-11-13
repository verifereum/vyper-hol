# extcall with gas=
interface Peer:
    def get(x: uint256) -> uint256: nonpayable

@external
def f(t: address, x: uint256, g: uint256) -> uint256:
    return extcall Peer(t).get(x, gas=g)
