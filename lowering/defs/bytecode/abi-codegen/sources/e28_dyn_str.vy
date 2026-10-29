# DynArray of String event field
event E:
    a: DynArray[String[5], 2]

@external
def f(x: DynArray[String[5], 2]):
    log E(a=x)
