# a10-11: materialize and hash each storage operand in order.
s: Bytes[40]
t: Bytes[40]
@external
def f() -> bool:
    return self.s == self.t
