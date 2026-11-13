from ethereum.ercs import IERC20Detailed

implements: IERC20Detailed

@external
@view
def name() -> String[1]:
    return "a"

@external
@view
def symbol() -> String[1]:
    return "b"

@external
@view
def decimals() -> uint8:
    return 18
