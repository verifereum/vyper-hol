# staticcall returning Bytes[64]
interface Peer:
    def data() -> Bytes[64]: view

@external
@view
def f(t: address) -> Bytes[64]:
    return staticcall Peer(t).data()
