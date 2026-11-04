@external
@pure
def f() -> bytes4:
    return method_id("transfer(address,uint256)", output_type=bytes4)
