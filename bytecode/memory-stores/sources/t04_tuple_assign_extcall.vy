# a11: tuple assignment from an external call
interface I:
    def g() -> (uint256, uint256): view

@external
def f(t: address) -> uint256:
    a: uint256 = 0
    b: uint256 = 0
    a, b = staticcall I(t).g()
    return a + b
