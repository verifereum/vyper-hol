# a10-03: storage dynamic array membership.
s: DynArray[uint256, 5]
@external
def f(x: uint256) -> bool:
    return x in self.s
