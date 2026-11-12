@external
@pure
def dynamic_roundtrip(
    text: String[16],
    data: Bytes[16],
) -> (String[16], Bytes[16]):
    return text, data
