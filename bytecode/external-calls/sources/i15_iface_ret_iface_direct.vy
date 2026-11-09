# interface method returning an interface type, result returned directly (no .address)
interface Other:
    def ping(): nonpayable

interface Peer:
    def next(p: Other) -> Other: view

@external
@view
def f(t: address) -> Other:
    return staticcall Peer(t).next(Other(t))
