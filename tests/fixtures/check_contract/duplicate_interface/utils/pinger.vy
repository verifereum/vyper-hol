from .interfaces import IPing

@internal
def _ping(target: address):
    extcall IPing(target).ping()
