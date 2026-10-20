# Issue #560 construction validation

## Independent inputs and reproduction

`sources/` retains the 66 named, complete Vyper
examples in the issue's witness-source section. `preparation.json` records the
pinned Vyper commit/settings, source hashes and Python acceptance or diagnostics.
`oracle/` is generated only by pinned Python Vyper, never from HOL output.
The additional `arr_dyn_lit_word` fixture is in the existing memory-store corpus.
The issue also references names such as `f02` and `g15` without complete source;
these are not fabricated or reported as tested.

Run these logical targets with holbuild, in this order:

1. `prepareMemoryConstructionMatrixTheory`: independently prepare the retained
   sources (optional one-time import via `MEMORY_CONSTRUCTION_TASK`).
2. `evalMemoryConstructionMatrixTheory`: stock frontend/checker in both modes,
   then HOL compilation and exact deploy/runtime comparisons. This diagnostic
   theory's successful build does **not** assert that every row matches.
3. `summarizeMemoryConstructionMatrixTheory`: produce `results.json`, including
   observed verdicts, section sizes/first differences, hashes and prerequisites.

Drivers locate the repository without worktree-specific paths. For actual
process execution, a pinned `vyper` on PATH and the usual Python dependencies
are required. The mandatory eleven fixture proofs are imported by
`evalCompilerMemoryStoresTheory`. `verifyMemoryConstructionFixturesTheory`
regenerates those independently and verifies the existing retained bytes.
`executeMemoryConstructionTheory` executes eight Vyper/HOL runtime pairs from
a different working directory, using `MEMORY_VALIDATION_PYTHON` or the local
`.venv-memory-validation/bin/python` (py-evm, eth_abi, eth_utils).

## Observations at this revision

- Full preexisting `evalCompilerBytecodeParityTheory` and
  `evalCompilerMemoryStoresTheory` build cleanly; the latter now additionally
  imports eleven exact construction fixture comparisons.
- All eleven mandatory fixtures MATCH. Eight EVM pairs pass: in particular
  `c10_assign_empty_struct.f(7)` returns 0 on both sides and
  `c11_annassign_empty_fixed_array.f(7)` returns 7 on both sides.
- Of 66 named matrix sources: 47 MATCH, 12 PARITY_DEFECT, 5 HOL NONE,
  1 HOL evaluation residual, 1 Python rejection (missing imported module).
  These are observations, not claims that unlanded dependency stacks work.
- Four bytestring-array return cases retain #551 ABI encoding differences.
- `p05_int_local_dynarray` retains the documented #545 internal-call residual;
  `x03_assign_elem_from_pop` retains #550 evaluation ordering.
- Nested/field append/pop cases retain #559 differences; `in_empty_list`
  retains #569 membership differences.
- Two constant aggregate cases compile to NONE without #565. Three immutable
  aggregate cases compile to NONE without #563; the fourth, `m05`, leaves an
  evaluation residual, so no byte verdict is claimed for it.
- `m38_const_in_type` cannot be prepared because the issue does not provide the
  imported `libp` source. Its Python rejection diagnostic is retained. The two
  main-module bound controls MATCH.

`results.tsv` records actual outcomes and `results.json` gives exact byte
section comparisons. Prerequisite labels classify the issue's documented
cross-issue boundaries; they are not proofs that applying those issues will
necessarily yield MATCH. No compiler semantics were changed to eliminate
these residuals. HOL `.term`/`.residual` files are disposable diagnostics, not
independent oracle data or logical proofs.
