error Msg:
    code: uint256
    text: String[64]
    data: Bytes[40]

@external
def fail(t: String[64], d: Bytes[40]):
    raise Msg(7, t, d)
