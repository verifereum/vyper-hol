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
- `sourceOrdinaryProgramCoreTestTheory`: paired `constant_bound.vy` and
  `constant_shifts.vy`, exact modules, deployment checking, independent artifacts
  and delete/poison invariance.
- `sourceShiftCountFrontendTestTheory`: strict JSON compatibility successes via
  the explicit legacy API. Independent full-Source checks are extracted with
  that optional feature; no translation fallback is introduced.
- `sourceShiftCountAudit.sml`: exported theorem-object audit rejecting hypotheses,
  axioms and oracle tags except the normal `DISK_THM` storage marker.

## Fixture provenance and reproduction

Run from the repository root with isolated environments for `VYPER_PIN`:

```sh
.agent-files/folded-value-validation/venv/bin/python -I tests/sourceShiftCountPin.py oracle
.agent-files/folded-value-validation/evm-venv/bin/python -I tests/sourceShiftCountPin.py execute
holbuild build sourceShiftCountTestTheory sourceOrdinaryProgramCoreTestTheory \
  sourceShiftCountFrontendTestTheory --tactic-timeout 2.5
holbuild run tests/sourceShiftCountAudit.sml
```

`oracle` checks installed compiler implementation bytes against `VYPER_PIN`,
independent acceptance expectations, and retained parser fixtures before
constant-qualifier erasure. Use `oracle --generate` only to regenerate those
fixtures. Prague executions exercise signed shifts, the legacy bound/exponent
function, canonical arithmetic counts and the uint8 count-expression overflow
revert. These are acceptance/execution tests, not bytecode-parity or complete
source-typing claims.
