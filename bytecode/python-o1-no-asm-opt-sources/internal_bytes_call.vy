@internal
@pure
def choose_bytes(data: Bytes[16], enabled: bool) -> Bytes[16]:
    if enabled:
        return data
    return b""

@external
@pure
def call_choose_bytes(data: Bytes[16], enabled: bool) -> Bytes[16]:
    return self.choose_bytes(data, enabled)
