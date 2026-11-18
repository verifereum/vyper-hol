
@external
def f(target: address) -> address:
    return create_from_blueprint(target, code_offset=as_wei_value(max_value(uint256) // 1000000000, "gwei"))
