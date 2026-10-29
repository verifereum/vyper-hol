# slice of a struct member named `code` (HOL is_extcode matches any Attribute "code")
struct S:
    code: Bytes[10]

@external
@pure
def f(s: S) -> Bytes[2]:
    return slice(s.code, 0, 2)
