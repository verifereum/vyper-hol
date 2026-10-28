# Source shift-count regression (#135 / #543)

`sourceExprElaborate` derives arithmetic operand context from independently
resolved runtime declarations. A literal's default uint256 does not force
`1 + n` to uint256 when `n` is uint8. Shift counts have their own type rather
than inheriting the signedness/width of the shifted value.

Constant counts use mathematical source evaluation and two original-tree
checks: unsigned source operator compatibility, and bounded arithmetic at an
independent candidate integer type. Only then is the canonical value coerced
at the runtime use. This accepts `(1 - 2) + 2` without accepting `-(0 - 1)`,
a signed runtime count, zero division, or `(1 << 256) >> 255`. Ordinary return
arithmetic still has its original contextual type/bounds; this is not blanket
permission to reify a convenient final value. `sourceExprDefs` applies the same
rule inside wholly constant shifts, including required constants. No source
constant evaluator operation or source-meaning definition changes.

Tests:

- `sourceShiftCountTestTheory`: typed expressions, canonical count coercion,
  required bounds and negative cases.
- `sourceShiftCountModuleTestTheory`: full pre-erasure source equivalents of
  existing `constant_bound.vy` and `constant_shifts.vy`, exact emitted modules,
  and successful deployment checking/composition.
- `sourceShiftCountFrontendTestTheory`: existing strict JSON fixtures through
  both legacy and `Source.check_constant_contract_file`, compared with those
  pre-erasure source equivalents. This target retains the legacy dependency
  chain and does not bypass a failing proof or use a translation fallback.
- Existing `sourceExprTestTheory` and `sourceModuleFrontendLibTestTheory`:
  full 37-expression and 37-module inventories (36 pin-valid modules accepted;
  `method_id_var` rejected as pinned).
- `sourceShiftCountAudit.sml`: exported theorem-object audit, rejecting all
  hypotheses, axioms and oracle tags except the ordinary DISK_THM marker.

Independent pin execution:

```sh
.agent-files/folded-value-validation/venv/bin/python -I tests/sourceShiftCountPin.py oracle
.agent-files/folded-value-validation/evm-venv/bin/python -I tests/sourceShiftCountPin.py execute
```

The oracle verifies the installed compiler's Python implementation bytes against
`VYPER_PIN`, checks 13 acceptance rows, and checks the retained parser fixtures
before erasure of constant qualifiers. `oracle --generate` regenerates only those
parser fixtures. Seven fresh Prague executions include signed shift results,
the legacy bound/exponent function, canonical arithmetic counts and the uint8
count-expression overflow revert. Receipt: `.agent-files/source-shift-pin.json`.
These are source acceptance/execution tests, not a claim of bytecode parity or
complete #135 source typing.
