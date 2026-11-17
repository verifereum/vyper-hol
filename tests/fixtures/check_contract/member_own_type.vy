# A field or element read into a wider context keeps its own type.
struct R:
    x0: DynArray[Bytes[5], 2]

@external
@pure
def foo(r: R) -> DynArray[Bytes[40], 2]:
    return r.x0

@external
@pure
def bar(a: DynArray[Bytes[5], 3]) -> Bytes[40]:
    return a[0]
