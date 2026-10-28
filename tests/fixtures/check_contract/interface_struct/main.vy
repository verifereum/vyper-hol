import I

m: HashMap[address, I.S]
modes: HashMap[address, I.Mode]
last: public(I.S)

@external
def put(x: address, v: uint256):
    self.m[x] = I.S(a=v)
    self.modes[x] = I.Mode.ON
    self.last = self.m[x]

@external
def clear(x: address):
    self.m[x] = empty(I.S)

@external
@view
def get(x: address) -> I.S:
    return self.m[x]

@external
@view
def mode(x: address) -> I.Mode:
    return self.modes[x]
