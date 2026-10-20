
event Seen:
    value: indexed(bytes20)

@external
def emit_value(data: bytes20):
    log Seen(value=data)
