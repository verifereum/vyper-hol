@internal
@pure
def combine(
    delta: int128,
    enabled: bool,
    tag: bytes4,
) -> (int128, bool, bytes4):
    return delta, enabled, tag

@external
@pure
def call_combine(
    delta: int128,
    enabled: bool,
    tag: bytes4,
) -> (int128, bool, bytes4):
    return self.combine(delta, enabled, tag)
