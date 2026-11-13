`slice_code_runtime.json` slices `self.code` with a runtime length, which the
checker rejects. Vyper rejects such a slice itself, so the fixture is edited by
hand: `slice_code_runtime.vy` was compiled with Vyper at `VYPER_PIN`
(`577d2534356903076bb79b5b15ebd4d772994693`) and sanitized as for the other
fixtures, then the slice's length node `4` was replaced by a copy of the `n`
node from `m: uint256 = n`.
