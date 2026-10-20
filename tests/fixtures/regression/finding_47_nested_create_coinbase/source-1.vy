
created: public(address)

@external
def create(blueprint: address):
    self.created = create_from_blueprint(blueprint)
