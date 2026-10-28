# Membership tests on static arrays whose slots hold the element type's
# default value (0 / empty(address)).
code = """
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
"""


def test_in_static_array_defaults(get_contract):
    c = get_contract(code)
    assert c.zero_in_literal() is True
    assert c.zero_not_in_literal() is False
    assert c.one_in_literal() is False
    assert c.zero_in_empty_local() is True
    assert c.empty_address_in_pair("0x0000000000000000000000000000000000000001") is True
    assert c.empty_address_in_pair("0x0000000000000000000000000000000000000000") is True
