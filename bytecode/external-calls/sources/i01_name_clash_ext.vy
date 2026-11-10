# interface method name equals an external function of this contract (different signature)
interface Peer:
    def get(x: uint256) -> uint256: view

@external
@view
def get(t: address) -> uint256:
    return staticcall Peer(t).get(5)
