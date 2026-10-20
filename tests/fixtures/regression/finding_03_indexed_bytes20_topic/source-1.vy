
event Seen:
    value: indexed(address)

@external
def emit_value(account: address):
    log Seen(value=account)
