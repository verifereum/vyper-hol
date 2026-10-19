# extcall with a memory-local composite default_return_value
interface Peer:
    def get() -> uint256[2]: nonpayable

@external
def f(t: address, x: uint256) -> uint256[2]:
    d: uint256[2] = [x, x]
    return extcall Peer(t).get(default_return_value=d)
