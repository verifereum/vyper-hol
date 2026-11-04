error Empty:
    pass

H: constant(Bytes[2]) = x"abcd"


@external
def poke() -> Bytes[2]:
    if len(H) == 0:
        raise Empty()
    return H
