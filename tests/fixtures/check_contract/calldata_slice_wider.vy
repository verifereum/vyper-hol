@external
@view
def wider(start: uint256) -> Bytes[100]:
    x: Bytes[100] = slice(msg.data, start, 4)
    return x
