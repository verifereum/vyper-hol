@external
@payable
def f(a: uint256 = msg.value + as_wei_value(57896044618658097711785492504343953926634992332820282019728792003956564819968, "wei"),
      b: bytes32 = sha256(b"abc"),
      c: uint256 = max(1, 2),
      d: uint256 = len(b"abc")) -> uint256:
    return a + c + d
