# staticcall returning a tuple with a dynamic member
interface Peer:
    def get() -> (uint256, String[10]): view

@external
@view
def f(t: address) -> (uint256, String[10]):
    return staticcall Peer(t).get()
