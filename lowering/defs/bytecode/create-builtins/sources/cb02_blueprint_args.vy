# create_from_blueprint with ctor args
@external
def foo(t: address, x: uint256, y: address) -> address:
    return create_from_blueprint(t, x, y)
