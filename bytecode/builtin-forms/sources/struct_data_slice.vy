# control: slice of a struct member named `data` (calldata struct decode)
struct S:
    data: Bytes[10]

@external
@pure
def f(s: S) -> Bytes[2]:
    return slice(s.data, 0, 2)
