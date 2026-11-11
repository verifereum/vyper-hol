# event declared in a builtin interface (IERC20.Transfer)
from ethereum.ercs import IERC20

@external
def f(x: uint256):
    log IERC20.Transfer(sender=msg.sender, receiver=self, value=x)
