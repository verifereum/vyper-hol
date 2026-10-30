# Source shift-count regressions

Shift counts have an independent type rather than inheriting the signedness or
width of the shifted value. Arithmetic operand context comes from independently
resolved runtime declarations: a literal's default uint256 must not force
`1 + n` to uint256 when `n` is uint8.

Constant counts use mathematical source evaluation plus original-tree checks
for unsigned operator compatibility and bounded arithmetic at an independent
candidate integer type. Only then is the canonical value coerced at runtime use.
This admits `(1 - 2) + 2`, but rejects `-(0 - 1)`, signed runtime counts, zero
division and `(1 << 256) >> 255`. Ordinary return arithmetic retains contextual
type/bounds. The same rule applies inside wholly constant shifts and required
constants; a convenient final value alone is insufficient.

## Regression purpose

- `sourceShiftCountTestTheory`: typed expressions, canonical count coercion,
  required bounds and negative cases.
- `sourceShiftCountModuleTestTheory`: pre-erasure equivalents of
  `constant_bound.vy` and `constant_shifts.vy`, exact emitted modules, deployment
  checking and composition.
- `sourceShiftCountFrontendTestTheory`: strict JSON fixtures through legacy and
  `Source.check_constant_contract_file`, compared with pre-erasure equivalents.
  This retains the legacy dependency chain, without a translation fallback.
- `sourceShiftCountAudit.sml`: exported theorem-object audit rejecting hypotheses,
  axioms and oracle tags except the normal `DISK_THM` storage marker.

## Fixture provenance and reproduction

Run from the repository root with isolated environments for `VYPER_PIN`:

```sh
.agent-files/folded-value-validation/venv/bin/python -I tests/sourceShiftCountPin.py oracle
.agent-files/folded-value-validation/evm-venv/bin/python -I tests/sourceShiftCountPin.py execute
holbuild build sourceShiftCountTestTheory sourceShiftCountModuleTestTheory \
  sourceShiftCountFrontendTestTheory --tactic-timeout 2.5
holbuild run tests/sourceShiftCountAudit.sml
```

`oracle` checks installed compiler implementation bytes against `VYPER_PIN`
and independent acceptance expectations. The HOL tests reuse the pre-erasure
captures in `fixtures/check_contract/source_ordinary/`, maintained by
`sourceOrdinaryPin.py`; no separate shift captures are needed.
Prague executions exercise signed shifts, the legacy bound/exponent
function, canonical arithmetic counts and the uint8 count-expression overflow
revert. These are acceptance/execution tests, not bytecode-parity or complete
source-typing claims.
