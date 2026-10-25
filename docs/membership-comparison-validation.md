# Membership and bytestring comparison validation (issue 569)

## Reproduction and independence

Run the opt-in kernel checks (the full matrix takes several minutes):

```
holbuild -j2 --maxheap=20000 build --tactic-timeout 30 \
  vyperMembershipAuditTestTheory membershipCheckerIntegrityTheory
```

The logical targets are `vyperMembershipParityTestTheory` (six named fixtures),
`vyperMembershipMatrixTestTheory` (controls, residual observations and checker
rejections), and `vyperMembershipAuditTestTheory` (tag audit and proof dependencies).
These are intentionally not added to the inexpensive default test roots.

The durable fixture bundle is `tests/fixtures/membership/`. `sources/` contains
all 30 Vyper programs, `inputs/` their sanitized annotated AST/layout JSON, and
`compiler/` independent Python compiler stdout/stderr and 27 deploy/runtime hex
pairs. The three other programs fail real code generation. The six requested
sources are retained here with the other task witnesses, rather than changing
the unrelated frozen 101-fixture corpus or its generator manifest.
`importMembershipFixturesLib` is a byte-for-byte import utility for the operator's
G0006 artifacts, not a HOL bytecode generator.

`compiler-provenance.json`, `compiler-source-audit.json` and
`artifact-sha256.json` retain compiler/input/output provenance. The independent
compiler is Vyper `0.5.0a4+cd74ce4f`, full commit
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`, with Python 3.11.11 and the six
constrained dependency versions. Settings: experimental codegen, optimization
NONE (O1 Venom pipeline), final assembly optimization disabled, Prague, no
bytecode metadata. The clean pinned checkout's installed Python sources were
hash-compared, excluding only generated `version.py` as documented by the audit.
The bundle's `report.json` records **artifact supply**, not HOL validation results.
The original `generate.py` is retained unchanged so every entry in the supplied
hash manifest is present; it is historical provenance and is never run by the
tests. The bundle contains 212 files, with 211 entries in the manifest (which
does not hash itself).

Both comparison scripts declare `fixtures/membership` through
`holbuild_extra_deps`, following the repository's existing marker-function
convention. This makes the fixture contents part of the build key and copies
them into each isolated theory stage. `membershipParityLib` first checks that
staged location, then the source-tree location. Neither compilation nor loading
requires `.agent-files`, a previous theory stage, or the original compiler
installation. When exporting sources, include the complete
`tests/fixtures/membership/` directory along with the scripts and libraries.

`membershipParityLib.program` runs `prepare_check_input` and `check_contract`
in both runtime and deploy modes before extracting the module. The new checker
predicate `is_prim_word_type_def` is registered in the private checker computation
set, alongside `well_typed_binop_def`; checking is not bypassed.

Expensive compiler computation is cached through kernel `EVAL_CONV` and the
existing `add_compile_eval` interface. That preparation receives only the
checked program, never expected bytecode. It evaluates the actual compiler,
including its guards, and checks the certificate's empty assumptions and exact
left-hand side. Independent expected bytes are read only for comparison. All
named parity theorems use `Proof EVAL_TAC QED`; neither a successful checker run
nor compiler normalization alone counts as MATCH.

## Observed matrix

MATCH below means **both deployment and runtime byte lists** equal the
independent compiler output, with HOL checker acceptance in both modes.

| Group | Witnesses | Result / kernel evidence |
|---|---|---|
| Required six fixtures | `in_lit_list`, `notin_lit_list3`, `in_mem_dynarray`, `in_storage_dynarray`, `eq_string_lit_same`, `eq_bytes_storage_both` | MATCH; six individual `*_matches_python` theorems in `vyperMembershipParityTest` |
| Additional task controls | `eq_string_storage_lhs_mem`, `eq_string_var`, `in_bytes4_list`, `in_calldata_sarray`, `in_dynarray_arg`, `in_flag`, `in_lit_list2`, `in_lit_zero`, `in_mem_sarray`, `in_sarray_zero`, `in_storage_sarray`, `list_in_lit`, `ne_bytes_lit_same`, `ne_bytes_var`, `notin_flag`, `notin_lit_list`, `notin_mem_sarray`, `notin_storage_dynarray` | MATCH; `task_controls_match_python` |
| Externally owned #549 witness | `eq_string_storage` | MATCH in this checkout; first component of `externally_owned_residual_observations` is T. The task's historical residual is not reproduced here; C6 makes no #549 implementation change. |
| Externally owned #560 witnesses | `in_empty_list`, `in_sarray_default` | PARITY_DEFECT, not MATCH; second and third observation components are F. `residual_compilation_succeeds` separately verifies HOL compilation is SOME, not NONE. |
| Non-word membership | `in_string_list`, `in_struct_dynarray`, `in_nested_array` | NOT_IN_DOMAIN: pinned Python codegen rejection retained in compiler stdout/stderr; HOL `nonword_witnesses_rejected_runtime` and `nonword_witnesses_rejected_deploy` establish checker result NONE. |

Thus there are 25 exact MATCH witnesses, two #560 residuals, and three
NOT_IN_DOMAIN witnesses. The additional `@pure` list and capacity-five DynArray
variants are explicitly included, not inferred from similar examples.

## Source semantics and element-domain evidence

`vyperMembershipSemanticsTest` proves the interpreter's sparse-zero literal and
local-array checks for **both In and NotIn** (`literal_membership_eval_test`,
`local_array_membership_eval_test`), the CPS local-array check, and pure and
constant-evaluator defaults/failure cases. In particular, source membership of
zero in `[0,1]` and `[7,0,5]` is true, and non-membership is false.

The aggregate behavior consistency experiment remains documented separately in
`membership-element-consistency.md` (operator G0003): 48 py-evm Prague executions
against kernel-derived semantic results, with equal/unequal In/NotIn cases,
literal-list and variable-array paths, word/flag controls and disclosed tuple
input limitations/reverts. That finite evidence, not Vyper rejection alone,
motivates the domain restriction. `membership_element_word_boundary` and
`membership_checker_lowering_boundary` connect the checker to lowering's word
predicate. The new matrix rechecks all three task aggregate witnesses **after**
the restriction; it does not compile rejected inputs by bypassing the checker.

## Proof integrity and scope

The audit target rebuilds affected proof consumers and checks `Tag.dest_tag`
on all registered results in `vyperMembershipParityTest`,
`vyperMembershipMatrixTest`, `vyperMembershipSemanticsTest`, `vyperSmallStep`,
`vyperTypeBuiltins` and `bytestringHashProps`, plus the exported list and
array membership instruction-trace theorems in `exprLoweringProps`. No oracle
other than the disk-loading marker is accepted. Component proof records C3/C4/C5
also establish the local membership/hash monotonicity lemmas, which are not
exported by the theory. Runtime/literal digest and hash comparison correctness
are provided by `bytestringHashProps`; comparison with source byte equality is
explicitly conditional on collision freedom, not an asserted injectivity of
Keccak.

This is not a proof of a universal end-to-end compiler correctness theorem.
Unchanged general admissions remain in `exprLoweringProps`:
`compile_expr_correct`, `compile_name_correct`, `compile_binop_correct`,
`compile_neg_correct`, and `compile_expr_ci_mono`, with downstream users of the
last admission. They are not used to establish these parity evaluations,
semantics results, instruction traces or bytestring hash correctness boundary.
No new admission is introduced, and this task does not claim those general
admissions have been discharged. `supported_binop` restrictions remain unchanged;
whitelist expansion belongs to #575. Finite exact bytecode equality and the
scoped correctness boundaries are not a substitute for that later work.

## Exported build verification (2026-10-23)

Two byte-identical source exports contained 1,847 nonignored repository files,
including the complete fixture bundle, and excluded `.agent-files` and previous
local build outputs. Both commands exited zero:

```
holbuild -j4 --maxheap=20000 build --tactic-timeout 30
holbuild -j2 --maxheap=20000 build --tactic-timeout 30 \
  vyperMembershipAuditTestTheory membershipCheckerIntegrityTheory
```

The full default build completed 864 actions (159 built, 705 restored).
The membership build completed 506 actions (126 built, 380 restored).
The parity, matrix and final audit theories executed afresh; matching cached
dependencies remained subject to the kernel-tag audits described above.
The six parity statements and all matrix statements are unchanged.

All 212 fixture files matched the independent originals in both exported trees
and in the two isolated comparison stages. All 211 manifest entries verified,
as did the pinned revision, 30 source hashes and 54 deployment/runtime bytecode
hashes and lengths. The original artifact-supply report and expected bytecode
were preserved unchanged.
