# send with a literal gas=
@external
@payable
def f(r: address):
    send(r, msg.value, gas=2300)
