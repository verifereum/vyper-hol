S: immutable(String[40])

@deploy
def __init__():
    S = "abc"

@external
def get() -> bytes32:
    return keccak256(S)
