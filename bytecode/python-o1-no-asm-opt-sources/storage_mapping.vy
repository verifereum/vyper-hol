anchor: uint256
balances: HashMap[address, uint256]

@external
def set_and_get(owner: address, x: uint256) -> uint256:
    self.balances[owner] = x
    return self.balances[owner]
