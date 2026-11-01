# aug-assign on transient array element (if accepted)
a: transient(uint256[3])

@external
def f(i: uint256) -> uint256:
    self.a[i] += 1
    return self.a[i]
