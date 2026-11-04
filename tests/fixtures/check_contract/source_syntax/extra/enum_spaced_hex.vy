enum Role:
    ADMIN
    USER

H: constant(Bytes[2]) = x"ab  cd"

role: public(Role)


@external
def promote():
    self.role = Role.ADMIN
