# w01: return an internal-call DynArray[Bytes[32], 2] as DynArray[Bytes[64], 2]
@internal
def g() -> DynArray[Bytes[32], 2]:
    return [b"ab", b"cdef"]

@external
def f() -> DynArray[Bytes[64], 2]:
    return self.g()
