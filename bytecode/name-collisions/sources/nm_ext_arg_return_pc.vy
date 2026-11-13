# external function argument named __return_pc__: must take the external
# (ABI RETURN) path, not the internal RET path (#557, a04-04)
@external
def f(__return_pc__: uint256) -> uint256:
    return __return_pc__ + 1
