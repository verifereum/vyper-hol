anchor: uint256
items: DynArray[uint256, 4]

@external
def append_write_pop(x: uint256) -> uint256:
    self.items.append(x)
    self.items[0] = x
    return self.items.pop()
