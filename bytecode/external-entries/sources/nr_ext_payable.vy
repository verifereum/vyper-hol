# @nonreentrant on a payable external function
@external
@payable
@nonreentrant
def f() -> uint256:
    return msg.value
