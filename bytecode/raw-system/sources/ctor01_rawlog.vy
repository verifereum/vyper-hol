# Literal and argument data exercise raw_log in deploy mode.
@deploy
def __init__(d: Bytes[8]):
    raw_log([], b"\x01")
    raw_log([], d)
@external
def foo() -> uint256:
    return 1
