# raw_log and raw_call in the constructor with argument data (deploy mode)
@deploy
def __init__(t: address, d: Bytes[8]):
    raw_log([], d)
    raw_call(t, d)
@external
def foo() -> uint256:
    return 1
