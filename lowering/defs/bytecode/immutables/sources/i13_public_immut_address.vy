# a01: public immutable address (owner pattern) plus external function
owner: public(immutable(address))

@deploy
def __init__():
    owner = msg.sender

@external
def is_owner() -> bool:
    return msg.sender == owner
