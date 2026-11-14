UPPER: constant(bytes32) = 0xABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABABAB
LOWER: constant(bytes32) = 0xabababababababababababababababababababababababababababababababab
ALIAS: constant(bytes32) = UPPER
TOPICS: constant(DynArray[bytes32, 2]) = [LOWER, UPPER]
FORWARD: constant(bool) = BOOLS[0]
BOOLS: constant(bool[1]) = [True]
FOUND: constant(bool) = ALIAS in [LOWER]
ABSENT: constant(bool) = ALIAS not in [LOWER]
SELECTED: constant(bool) = TOPICS[1] in [LOWER]

@external
@pure
def values() -> (bool, bool, bool, bool):
    return FOUND, ABSENT, SELECTED, FORWARD

@external
def emit():
    raw_log(TOPICS, b"")
    raw_log([[UPPER]][0], b"")
