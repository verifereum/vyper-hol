# a11: assign a storage fixed array to a local array (storage->memory copy)
arr: uint256[3]

@external
def f(i: uint256) -> uint256:
    a: uint256[3] = [0, 0, 0]
    a = self.arr
    return a[i]
