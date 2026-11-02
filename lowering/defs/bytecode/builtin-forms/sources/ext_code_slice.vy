# slice(addr.code, s, 10): start (and the output buffer) are lowered before
# the address.  The length must be a literal: .code has no static bound.
@external
@view
def f(a: address, s: uint256) -> Bytes[10]:
    return slice(a.code, s, 10)
