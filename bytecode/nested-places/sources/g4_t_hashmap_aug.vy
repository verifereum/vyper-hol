m: transient(HashMap[address, uint256])

@external
def f(k: address) -> uint256:
    self.m[k] += 1
    return self.m[k]
