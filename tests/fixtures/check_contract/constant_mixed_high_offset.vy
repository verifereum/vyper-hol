@external
def f(target: address) -> address:
    return create_from_blueprint(target, code_offset=max_value(uint256) - (len([b"a",x"61"][0]) - 1))
