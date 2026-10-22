# external function `get` declared BEFORE an interface with a same-named method of a different signature
@external
@view
def get(t: address) -> uint256:
    return staticcall Peer(t).get(5)

interface Peer:
    def get(x: uint256) -> uint256: view
