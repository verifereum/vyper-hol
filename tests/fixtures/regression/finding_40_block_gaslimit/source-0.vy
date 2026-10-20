
@external
@view
def block_limit() -> uint256:
    return block.gaslimit

@external
@view
def number_control() -> uint256:
    return block.number
