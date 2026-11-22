# Vyper semantic regressions

Keep executable pytest scenarios here, grouped by semantic area and named for the
behavior they exercise. Add each scenario in the same commit as its semantics fix.
Unfixed divergences belong in issues, not in the enabled test suite.

`hand/` holds cases whose expected results are written from the language rules
rather than taken from a compiler: each test cites the sentence of Vyper's
documentation at `VYPER_PIN`, or the section of the Solidity ABI specification,
its expectation follows from.

The pinned export generator temporarily copies this directory into
`tests/functional/codegen/vyper_hol_regression/` for a default full-suite export
and removes the copy afterwards. It makes each copied directory a package, so a
scenario file may share its name with an upstream test. For that, it refuses a
directory whose name isn't a Python identifier or that has a same-named `.py`
file beside it. Focused `--test`/`--fixture` exports do not add these
regressions. Export provenance and the cache key include every regression pytest
source, as well as the pin and semantics profile.
Do not commit exported JSON, duplicated Vyper source, or generated HOL wrappers.

Follow the inline generation command in the repository README after building
`vyperTestLib` and exporting the tests. The generated `vyperTest_*` theories join
the normal CI matrix. Large suites are split into independent parts bounded by
100 tests and 262144 binary payload hex characters; an oversized test gets its own
part. Generation updates only the definition call in an existing split suite,
preserving its other proofs and annotations. Small custom definition scripts
remain unchanged. Test wrappers are regenerated.
