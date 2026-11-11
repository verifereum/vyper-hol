interface I:
    def g() -> uint256: view

m: HashMap[uint256, uint256]

@external
def f(a: address, k: uint256):
    self.m[k] = staticcall I(a).g()
