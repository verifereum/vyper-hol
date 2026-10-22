from ..utils.interfaces import IPing
from ..utils import pinger

@external
def f(target: address):
    extcall IPing(target).ping()
    pinger._ping(target)
