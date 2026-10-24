# extcall with value=, default_return_value= and gas=, in that order
interface Peer:
    def get(x: uint256) -> uint256: payable

@external
def f(t: address, x: uint256, v: uint256, d: uint256, g: uint256) -> uint256:
    return extcall Peer(t).get(x, value=v, default_return_value=d, gas=g)
