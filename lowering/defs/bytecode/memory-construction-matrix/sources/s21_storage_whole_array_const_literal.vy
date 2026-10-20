# a11: control for s07: whole fixed storage array assigned from a constant literal (no argument read)
arr: uint256[3]

@external
def f():
    self.arr = [1, 2, 3]
