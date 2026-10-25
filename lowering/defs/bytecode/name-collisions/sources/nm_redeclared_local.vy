# a local re-declared with a different type in a disjoint block gets its own
# allocation of its own size in each block (#644)
@external
def f(c: bool) -> uint256:
    if c:
        a: Bytes[100] = b"hello"
        return len(a)
    else:
        a: uint256 = 1
        return a
