@external
@view
def get_sender() -> address:
    return msg.sender

@external
@view
def get_self_address() -> address:
    return self

@external
@payable
def get_value_sent() -> uint256:
    return msg.value
