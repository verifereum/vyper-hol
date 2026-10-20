"""Finding 3: bytes20 and address use different indexed-event padding."""

BYTES20_EVENT = """
event Seen:
    value: indexed(bytes20)

@external
def emit_value(data: bytes20):
    log Seen(value=data)
"""

ADDRESS_EVENT = """
event Seen:
    value: indexed(address)

@external
def emit_value(account: address):
    log Seen(value=account)
"""


def test_indexed_bytes20_is_right_padded_but_address_is_left_padded(get_contract, env):
    bytes_value = b"\x11" * 20

    bytes_contract = get_contract(BYTES20_EVENT)
    bytes_contract.emit_value(bytes_value)
    ((bytes_topics, bytes_data),) = env.get_logs(bytes_contract, raw=True)
    assert bytes_topics[1] == bytes_value + bytes(12)
    assert bytes_data == b""

    address_contract = get_contract(ADDRESS_EVENT)
    address_contract.emit_value("0x" + "11" * 20)
    ((address_topics, address_data),) = env.get_logs(address_contract, raw=True)
    assert address_topics[1] == bytes(12) + bytes_value
    assert address_data == b""
