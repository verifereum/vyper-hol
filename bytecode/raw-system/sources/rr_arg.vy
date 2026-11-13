# @raw_return echoing calldata bytes argument
@external
@raw_return
def f(b: Bytes[100]) -> Bytes[100]:
    return b
