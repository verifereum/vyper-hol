import lib2

interface IFace:
    def foo() -> uint256: view
    def g() -> uint256: view

implements: IFace

exports: lib2.foo

x: public(uint256)


@deploy
def __init__():
    self.x = 3


@external
@view
def g() -> uint256:
    return self.x
