# w03: log an internal-call DynArray[Bytes[32], 2] as a DynArray[Bytes[64], 2] field
event E:
    xs: DynArray[Bytes[64], 2]

@internal
def g() -> DynArray[Bytes[32], 2]:
    return [b"ab", b"cdef"]

@external
def f():
    log E(xs=self.g())
