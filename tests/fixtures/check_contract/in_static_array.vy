@external
@view
def zero_in_literal() -> bool:
    return 0 in [0, 7]

@external
@view
def zero_not_in_literal() -> bool:
    return 0 not in [0, 7]

@external
@view
def one_in_literal() -> bool:
    return 1 in [0, 7]

@external
@view
def zero_in_empty_local() -> bool:
    x: uint256[3] = empty(uint256[3])
    return 0 in x

@external
@view
def empty_address_in_pair(a: address) -> bool:
    return empty(address) in [a, empty(address)]
