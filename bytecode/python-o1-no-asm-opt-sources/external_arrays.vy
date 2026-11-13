@external
@pure
def fixed_roundtrip(values: int128[3]) -> int128[3]:
    return values

@external
@pure
def dynamic_roundtrip(values: DynArray[bytes4, 3]) -> DynArray[bytes4, 3]:
    return values
