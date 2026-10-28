items: HashMap[uint256, DynArray[uint256, 4]]

@external
def take(bucket: uint256) -> uint256:
    return self.items[bucket].pop()

@external
def roundtrip() -> uint256:
    self.items[7] = [11, 23]
    return self.items[7].pop()
