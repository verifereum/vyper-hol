@external
@pure
def word() -> bytes4:
    return method_id("transfer(address,uint256)", output_type=bytes4)
@external
@pure
def buf() -> Bytes[4]:
    return method_id("transfer(address,uint256)")
