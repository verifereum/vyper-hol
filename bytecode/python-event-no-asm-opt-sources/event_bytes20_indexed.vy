event E:
    a: indexed(bytes20)

@external
def f(x: bytes20):
    log E(x)
