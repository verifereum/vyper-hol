event E:
    a: DynArray[String[5], 2]

@external
def f(x: DynArray[String[3], 2]):
    log E(x)
