# interface method returning an interface type and taking one as argument
interface Other:
    def ping(): nonpayable

interface Peer:
    def next(p: Other) -> Other: view

@external
@view
def f(t: address) -> address:
    o: Other = staticcall Peer(t).next(Other(t))
    return o.address
