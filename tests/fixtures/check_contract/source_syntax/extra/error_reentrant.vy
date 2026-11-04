#pragma nonreentrancy on

error Unauthorized:
    caller: address
    code: uint256

value: reentrant(public(uint256))


@external
def poke():
    raise Unauthorized(msg.sender, 1)
