@external
def deploy(target: address) -> address:
    return create_from_blueprint(target, code_offset=len([b"a", x"61"][0]))
