# extcall with a literal gas=
interface Peer:
    def get() -> uint256: nonpayable

@external
def f(t: address) -> uint256:
    return extcall Peer(t).get(gas=50000)
