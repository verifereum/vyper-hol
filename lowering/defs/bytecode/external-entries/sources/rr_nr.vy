# @raw_return combined with @nonreentrant
@external
@nonreentrant
@raw_return
def f(b: Bytes[100]) -> Bytes[100]:
    return b
