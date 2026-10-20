
@external
@view
def direct() -> (uint256, bytes32, bool, uint256):
    return self.codesize, self.codehash, self.is_contract, self.balance

@external
@view
def through_address(target: address) -> (uint256, bytes32, bool, uint256):
    return target.codesize, target.codehash, target.is_contract, target.balance
