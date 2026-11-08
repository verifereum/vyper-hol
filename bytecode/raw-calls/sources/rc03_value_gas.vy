# raw_call with value= and gas= kwargs (statement)
@external
@payable
def foo(t: address, v: uint256, g: uint256):
    raw_call(t, b"", value=v, gas=g)
