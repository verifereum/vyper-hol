# a14 (from a07): uint2str result used in concat (a14-01 + a07 residual)
@external
@pure
def f(x: uint256) -> String[90]:
    return concat("n=", uint2str(x))
