# A folded denomination conversion uses the literal blueprint check.
@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=as_wei_value(max_value(uint256) // 1000000000, "gwei"))
