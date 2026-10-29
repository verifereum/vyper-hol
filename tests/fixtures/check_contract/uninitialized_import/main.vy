import lib
import mid

initializes: mid


@deploy
def __init__():
    mid.__init__(3)


@external
@pure
def f(a: uint256) -> uint256:
    return lib.double(a)


@external
@view
def g(a: uint256) -> uint256:
    return mid.scaled(a)
