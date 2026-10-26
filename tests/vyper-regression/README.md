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
the normal CI matrix. Generation preserves existing definition scripts, including
their JSON/CV proof boundaries, and creates definitions for newly exported
regressions. Test wrappers are regenerated.
