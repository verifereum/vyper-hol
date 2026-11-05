OWNER: constant(address) = 0x0000000000000000000000000000000000000001

@external
def f() -> address:
    return OWNER
