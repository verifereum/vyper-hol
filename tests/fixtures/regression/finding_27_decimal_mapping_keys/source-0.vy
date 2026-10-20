
values: HashMap[decimal, uint256]
nested: HashMap[uint256, HashMap[decimal, uint256]]

@external
def direct() -> uint256[4]:
    self.values[1.0] = 11
    self.values[2.0] = 22
    self.values[-1.5] = 33
    return [self.values[1.0], self.values[2.0], self.values[-1.5], self.values[0.0]]

@external
def through_outer_key() -> uint256[4]:
    self.nested[7][1.0] = 11
    self.nested[7][2.0] = 22
    self.nested[8][1.0] = 33
    return [self.nested[7][1.0], self.nested[7][2.0], self.nested[8][1.0], self.nested[8][0.0]]
