import lib

ALIAS: constant(bytes32) = lib.ALIAS
FOUND: constant(bool) = ALIAS in [lib.LOWER]
ABSENT: constant(bool) = lib.TOPICS[1] not in [lib.LOWER]

@external
@pure
def values() -> (bool, bool):
    return FOUND, ABSENT

@external
def emit():
    raw_log(lib.TOPICS, b"")
