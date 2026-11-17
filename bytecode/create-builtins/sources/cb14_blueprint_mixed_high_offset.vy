# Refused folding must survive arithmetic around the selected length.
@external
def foo(t: address) -> address:
    return create_from_blueprint(t, code_offset=max_value(uint256) - (len([b"a", x"61"][0]) - 1))
