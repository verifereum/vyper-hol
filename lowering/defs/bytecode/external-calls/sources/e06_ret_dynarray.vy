# staticcall returning DynArray[uint256, 3]
interface Peer:
    def items() -> DynArray[uint256, 3]: view

@external
@view
def f(t: address) -> DynArray[uint256, 3]:
    return staticcall Peer(t).items()
