@external
def call(a: address) -> Bytes[32]:
    return raw_call(a, b"", max_outsize=32, is_static_call=True or False)
