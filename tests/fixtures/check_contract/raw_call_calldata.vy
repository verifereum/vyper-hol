# Pinned Vyper cd74ce4f: original calldata and folded keyword metadata.
OUTSIZE: constant(uint256) = 4
REVERT: constant(bool) = False

@external
@payable
def forward(target: address, amount: uint256):
    raw_call(target, msg.data, value=amount)

@external
@view
def static_result(target: address) -> Bytes[4]:
    return raw_call(target, msg.data, max_outsize=OUTSIZE, is_static_call=True)

@external
def status(target: address) -> bool:
    return raw_call(target, msg.data, revert_on_failure=REVERT)

@external
def output(target: address) -> (bool, Bytes[4]):
    return raw_call(target, msg.data, max_outsize=2 + 2, revert_on_failure=False)
