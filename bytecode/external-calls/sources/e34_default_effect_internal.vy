# extcall default_return_value calling a state-mutating internal function (eager in real)
c: uint256
@internal
def bump() -> uint256:
    self.c += 1
    return self.c

interface Peer:
    def get() -> uint256: nonpayable

@external
def f(t: address) -> uint256:
    return extcall Peer(t).get(default_return_value=self.bump())
