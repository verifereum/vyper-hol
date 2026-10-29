# convert(address, bytesM) treats the address as the 160-bit integer it
# denotes, so the address lands in the low bytes: bytesM left-pads it.
# A bytes20 source is a byte string and right-pads instead.


def test_convert_address_to_bytes_m_left_pads(env, get_contract):
    code = """
stored: address

@deploy
def __init__():
    self.stored = msg.sender

@external
@view
def arg_to_bytes32(a: address) -> bytes32:
    return convert(a, bytes32)

@external
@view
def arg_to_bytes21(a: address) -> bytes21:
    return convert(a, bytes21)

@external
@view
def arg_to_bytes20(a: address) -> bytes20:
    return convert(a, bytes20)

@external
@view
def stored_to_bytes32() -> bytes32:
    return convert(self.stored, bytes32)

@external
@view
def sender_to_bytes32() -> bytes32:
    return convert(msg.sender, bytes32)

@external
@view
def bytes20_to_bytes32(b: bytes20) -> bytes32:
    return convert(b, bytes32)
    """
    c = get_contract(code)
    deployer = env.deployer
    a = env.accounts[1]
    a_bytes = bytes.fromhex(a[2:])
    deployer_bytes = bytes.fromhex(deployer[2:])

    assert c.arg_to_bytes32(a) == b"\x00" * 12 + a_bytes
    assert c.arg_to_bytes21(a) == b"\x00" + a_bytes
    assert c.arg_to_bytes20(a) == a_bytes
    assert c.stored_to_bytes32() == b"\x00" * 12 + deployer_bytes
    assert c.sender_to_bytes32(sender=a) == b"\x00" * 12 + a_bytes
    assert c.bytes20_to_bytes32(a_bytes) == a_bytes + b"\x00" * 12
