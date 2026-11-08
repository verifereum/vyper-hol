import iface

@external
def call_f(target: address):
    extcall iface(target).f([1], "a")
