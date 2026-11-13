# @nonreentrant on a view external function (check only, no lock store)
x: uint256

@external
@view
@nonreentrant
def f() -> uint256:
    return self.x
