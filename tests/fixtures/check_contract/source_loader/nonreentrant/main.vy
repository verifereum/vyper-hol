#pragma nonreentrancy on

@external
def locked():
    pass

@external
@reentrant
def unlocked():
    pass

@external
@pure
def pure_value() -> uint256:
    return 1

@internal
def helper():
    pass

@deploy
def __init__():
    pass
