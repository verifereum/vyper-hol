# interface method with a default parameter, called with fewer args
interface Peer:
    def get(x: uint256, y: uint256 = 3) -> uint256: view

@external
@view
def f(t: address) -> uint256:
    return staticcall Peer(t).get(1)
