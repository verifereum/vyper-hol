event Mixed:
    owner: indexed(address)
    label: indexed(String[16])
    tag: indexed(bytes4)
    delta: int128
    enabled: bool
    payload: Bytes[16]

@external
def emit_mixed(
    owner: address,
    label: String[16],
    tag: bytes4,
    delta: int128,
    enabled: bool,
    payload: Bytes[16],
):
    log Mixed(owner=owner, label=label, tag=tag, delta=delta, enabled=enabled, payload=payload)
