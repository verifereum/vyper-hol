# two interfaces declaring the same method name with different signatures; call the second
interface A:
    def get(x: uint256) -> uint256: view

interface B:
    def get(x: address) -> uint256: view

@external
@view
def f(t: address) -> uint256:
    return staticcall B(t).get(t)
