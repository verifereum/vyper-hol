# extcall default_return_value with a side-effecting (extcall) default: real evaluates it eagerly before the call
interface Peer:
    def get() -> uint256: nonpayable
    def bump() -> uint256: nonpayable

@external
def f(t: address) -> uint256:
    return extcall Peer(t).get(default_return_value=extcall Peer(t).bump())
