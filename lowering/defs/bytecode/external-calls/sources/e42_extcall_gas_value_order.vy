# extcall with gas= before value=: keyword operands are lowered in source order
interface Peer:
    def get(x: uint256) -> uint256: payable

@external
def f(t: address, x: uint256, g: uint256, v: uint256) -> uint256:
    return extcall Peer(t).get(x, gas=g, value=v)
