# a16 m49_erc20_event: log of the builtin IERC20.Approval event (like a12 e62) with a non-indexed field
from ethereum.ercs import IERC20

@external
def f(s: address, x: uint256):
    log IERC20.Approval(owner=msg.sender, spender=s, value=x)
