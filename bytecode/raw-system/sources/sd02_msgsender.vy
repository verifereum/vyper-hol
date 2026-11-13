# selfdestruct to msg.sender inside if
@external
def foo(x: uint256):
    if x == 1:
        selfdestruct(msg.sender)
