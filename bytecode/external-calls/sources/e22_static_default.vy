# staticcall with default_return_value
interface Peer:
    def get() -> uint256: view

@external
@view
def f(t: address) -> uint256:
    return staticcall Peer(t).get(default_return_value=7)
