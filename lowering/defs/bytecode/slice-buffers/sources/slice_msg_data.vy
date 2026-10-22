# slice of msg.data with literal args (CalldataSlice)
@external
@view
def f() -> Bytes[4]:
    return slice(msg.data, 0, 4)
