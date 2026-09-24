interface AccountLike:
    def ping() -> uint256: view

@external
@view
def account_address(a: AccountLike) -> address:
    return a.address

@external
@view
def account_balance(a: address) -> uint256:
    return a.balance

@external
@view
def account_codehash(a: address) -> bytes32:
    return a.codehash

@external
@view
def account_codesize(a: address) -> uint256:
    return a.codesize

@external
@view
def account_is_contract(a: address) -> bool:
    return a.is_contract
