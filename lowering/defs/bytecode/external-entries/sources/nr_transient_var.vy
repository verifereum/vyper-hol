# nonreentrant plus a user transient variable (key takes transient slot 0)
t: transient(uint256)

@external
@nonreentrant
def f(a: uint256) -> uint256:
    self.t = a
    return self.t
