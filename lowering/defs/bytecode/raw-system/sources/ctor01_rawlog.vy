# raw_log and raw_call in the constructor (deploy mode)
@deploy
def __init__(t: address):
    raw_log([], b"\x01")
    raw_call(t, b"")
@external
def foo() -> uint256:
    return 1
