# default_return_value given by a conditional expression
interface Peer:
    def get() -> uint256: nonpayable

@external
def f(t: address, c: bool, a: uint256, b: uint256) -> uint256:
    return extcall Peer(t).get(default_return_value=a if c else b)
