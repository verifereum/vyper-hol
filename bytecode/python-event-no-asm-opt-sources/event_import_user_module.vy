# a16 m14_event_user_module: log of an event declared in a user-written imported module
import libp

@external
def f(x: uint256):
    log libp.Ev(who=msg.sender, v=x)
