# create_from_blueprint with ctor args and salt
@external
def foo(t: address, x: uint256, s: bytes32) -> address:
    return create_from_blueprint(t, x, salt=s)
