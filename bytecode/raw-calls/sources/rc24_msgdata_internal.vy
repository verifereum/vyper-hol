# raw_call(msg.data) inside an internal function
@internal
def h(t: address):
    raw_call(t, msg.data)
@external
def foo(t: address):
    self.h(t)
