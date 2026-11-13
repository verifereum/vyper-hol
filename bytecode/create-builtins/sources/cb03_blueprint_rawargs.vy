# create_from_blueprint raw_args=True
@external
def foo(t: address, d: Bytes[64]) -> address:
    return create_from_blueprint(t, d, raw_args=True)
