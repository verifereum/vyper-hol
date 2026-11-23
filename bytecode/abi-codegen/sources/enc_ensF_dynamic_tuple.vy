@external
@pure
def encode_dynamic(text: String[16], payload: Bytes[16]) -> Bytes[196]:
    value: (String[16], Bytes[16]) = (text, payload)
    return abi_encode(value, ensure_tuple=False, method_id=0xdeadbeef)
