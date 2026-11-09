# create_from_blueprint no ctor args
@external
def foo(t: address) -> address:
    return create_from_blueprint(t)
