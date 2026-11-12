# create_from_blueprint revert_on_failure=False with arg
@external
def foo(t: address, x: uint256) -> address:
    return create_from_blueprint(t, x, revert_on_failure=False)
