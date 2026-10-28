# Same declarations as interface_struct_return/main.vy at VYPER_PIN.
# The obsolete version directive is omitted.
import manager

@external
@view
def read(addr: address) -> uint256:
    record: manager.Record = staticcall manager(addr).get_record()
    return record.value
