# extcall with default_return_value of a composite type
interface Peer:
    def get() -> uint256[2]: nonpayable

@external
def f(t: address) -> uint256[2]:
    return extcall Peer(t).get(default_return_value=[1, 2])
