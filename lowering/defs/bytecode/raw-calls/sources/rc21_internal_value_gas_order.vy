# raw_call with gas= before value= (kwarg evaluation order) using internal calls
c: uint256
@internal
def g() -> uint256:
    self.c = 1
    return 100000
@internal
def v() -> uint256:
    self.c = 2
    return 0
@external
def foo(t: address):
    raw_call(t, b"", gas=self.g(), value=self.v())
