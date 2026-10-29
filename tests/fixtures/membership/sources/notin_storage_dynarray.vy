# a10: x not in storage DynArray
s: DynArray[address, 3]
@external
def f(x: address) -> bool:
    return x not in self.s
