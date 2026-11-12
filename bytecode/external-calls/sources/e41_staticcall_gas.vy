# staticcall with gas=
interface Peer:
    def get(x: uint256) -> uint256: view

@external
@view
def f(t: address, x: uint256, g: uint256) -> uint256:
    return staticcall Peer(t).get(x, gas=g)
