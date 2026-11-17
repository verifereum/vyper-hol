import IFoo
import IBar
implements: IFoo
implements: IBar

@external
@view
def foo() -> uint256:
    return 1

@external
@view
def bar() -> uint256:
    return 2
