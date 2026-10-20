
@external
@view
def modern() -> bytes32:
    return block.prevrandao

@external
@view
def legacy() -> uint256:
    return block.difficulty

@external
@view
def number_control() -> uint256:
    return block.number
