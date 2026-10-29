# mutation base: DynArray[String[5], 2] argument (mutated to String[5][2], which Vyper rejects)
@external
@pure
def f(x: DynArray[String[5], 2]) -> uint256:
    return 1
