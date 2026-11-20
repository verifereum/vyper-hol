#pragma enable-decimals

balances: HashMap[decimal, uint256]

@external
def store(key: decimal, amount: uint256):
    self.balances[key] = amount
