interface Peer:
    def inspect(delta: int128, enabled: bool) -> (int128, bool): view
    def update(x: uint256) -> bool: payable

@external
@view
def query_peer(target: address, delta: int128, enabled: bool) -> (int128, bool):
    return staticcall Peer(target).inspect(delta, enabled)

@external
@payable
def update_peer(target: address, x: uint256) -> bool:
    return extcall Peer(target).update(x, value=msg.value)
