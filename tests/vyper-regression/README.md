# Vyper semantic regressions

Keep executable pytest scenarios here, grouped by semantic area and named for the
behavior they exercise. Add each scenario in the same commit as its semantics fix.
Unfixed divergences belong in issues, not in the enabled test suite.

The pinned Vyper export action copies this directory into
`tests/functional/codegen/vyper_hol_regression/` before invoking upstream pytest
with `--export`. The export cache includes both `VYPER_PIN` and the pytest sources.
Do not commit exported JSON, duplicated Vyper source, or generated HOL wrappers.

From `tests/`, run `holbuild run --noconfig generateVyperTests.sml` after building
`vyperTestLib` and exporting the tests. The generated `vyperTest_*` theories join
the normal CI matrix.

Upstream traces contain call results but not expected logs or final accounts.
A same-named `.sml` file may add HOL state assertions for its pytest. These files
use `regression_traces` (the generated trace constants) and the focused helpers in
`vyperRegressionStateTheory`; they supplement, rather than replace, ordinary
trace replay. Keep these checks until the upstream export records those fields.
