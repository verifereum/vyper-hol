# Vyper semantic regressions

Keep executable pytest scenarios here, grouped by semantic area and named for the
behavior they exercise. Add each scenario in the same commit as its semantics fix.
Unfixed divergences belong in issues, not in the enabled test suite.

The pinned export generator temporarily copies this directory into
`tests/functional/codegen/vyper_hol_regression/` for a default full-suite export
and removes the copy afterwards. Focused `--test`/`--fixture` exports do not add
these regressions. Export provenance and the cache key include every regression
pytest source, as well as the pin and semantics profile.
Do not commit exported JSON, duplicated Vyper source, or generated HOL wrappers.

Follow the inline generation command in the repository README after building
`vyperTestLib` and exporting the tests. The generated `vyperTest_*` theories join
the normal CI matrix. Generation regenerates definition and replay scripts as
independent batches of at most 100 tests, including newly exported regressions.
Hand-written proof suffixes following `(* ===== Local regression proofs ===== *)`
are preserved, including their JSON/CV proof boundaries.
