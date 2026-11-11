# extcall with default_return_value
interface Peer:
    def get() -> uint256: nonpayable

@external
def f(t: address) -> uint256:
    return extcall Peer(t).get(default_return_value=7)
