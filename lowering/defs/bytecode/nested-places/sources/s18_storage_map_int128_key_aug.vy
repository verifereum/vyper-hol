m: HashMap[int128, uint256]

@external
def f(k: int128, x: uint256):
    self.m[k] += x
