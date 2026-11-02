# create_from_blueprint raw_args=True with a bytes32 argument
@external
def foo(t: address, x: bytes32) -> address:
    return create_from_blueprint(t, x, raw_args=True)
