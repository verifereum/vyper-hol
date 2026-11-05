# Membership and bytestring comparison validation

The fixture bundle keeps 12 programs covering the comparison lowering branches.
Eleven have independent Python compiler deployment/runtime bytecode; one is an
aggregate-membership input rejected by both the Python compiler and HOL checker.
The six core parity tests remain unchanged. Additional concrete variants were
removed where the retained cases exercise the same branch.

## Retained cases

| Fixture | Coverage |
|---|---|
| `in_lit_list` | Literal-list comparisons and left-folded membership |
| `notin_lit_list3` | Three variable comparisons and complemented fold |
| `in_mem_dynarray` | Memory dynamic-array loop and entry bound check |
| `in_storage_dynarray` | Storage dynamic-array membership |
| `eq_string_lit_same` | Runtime string against a compile-time literal hash |
| `eq_bytes_storage_both` | Ordered materialization and hashing of both storage operands |
| `in_flag` | Direct flag membership |
| `notin_flag` | Complemented flag membership |
| `notin_mem_sarray` | Fixed-array loop, narrow word elements and array non-membership |
| `ne_bytes_var` | Runtime bytestring inequality |
| `in_empty_list` | Empty dynamic-array exit |
| `in_nested_array` | Aggregate-element rejection in runtime and deploy modes |

The first six have individual `*_matches_python` theorems in
`vyperMembershipParityTest`. The next five are checked together by
`task_controls_match_python` in `vyperMembershipMatrixTest`. Each comparison
checks both deployment and runtime byte lists. The matrix also checks the final
case with `nonword_witnesses_rejected_runtime` and
`nonword_witnesses_rejected_deploy`.

The former historical-residual group is no longer a separate test product:
its empty-array case is included in the controls, whose exact equality also
establishes successful compilation. Other removed cases included repeated list
lengths, capacities and mutability annotations, additional operand/type variants,
and string/struct concrete rejections. This is a smaller finite regression set;
it does not claim those removed concrete examples were rechecked.

## Fixture provenance

`tests/fixtures/membership/` contains 40 files: 12 sources, 12 sanitized annotated
AST/layout inputs, 11 deployment/runtime hex pairs, one compiler rejection
diagnostic, and four shared inventory/provenance files. The manifest hashes the
other 39 files. Retained sources, inputs, expected bytes and rejection diagnostics
are unchanged; only the inventories were filtered to the retained cases.

The independent compiler is Vyper `0.5.0a4+cd74ce4f`, commit
`cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`, with Python 3.11.11 and the six
dependency versions recorded in `compiler-provenance.json`. Settings are
experimental codegen, optimization NONE with the O1 Venom pipeline, final assembly
optimization disabled, Prague, and no bytecode metadata.

`compiler-source-audit.json` records the compiler source hashes.
`compiler-provenance.json` retains each remaining case's original commands,
source hash, exit codes and output hashes. `report.json` is an artifact inventory,
not a record of HOL validation results.

The comparison theories declare the fixture directory with `holbuild_extra_deps`
so isolated builds receive and hash their inputs. `membershipParityLib.program`
checks each successful input in runtime and deploy modes before compilation.
`prepare_compile` derives a kernel evaluation certificate from the actual
compiler and checked program, without reading expected bytecode. The named parity
theorems compare that result against the independent bytes with `EVAL_TAC`.

## Semantic checks and proof integrity

`vyperMembershipSemanticsTest` remains in the default test ancestor theory.
It checks sparse-zero literal and local-array semantics for both operators,
the CPS path, and pure/constant evaluator defaults and failures. Its symbolic
checker boundary tests retain primitive-word and flag acceptance plus rejection
of strings, dynamic bytes, structs, tuples, nested arrays and oversized fixed
bytes. Reducing the fixture set does not change these statements.

`membershipCheckerIntegrity` audits the checker and typing dependencies.
`vyperMembershipAuditTest` checks oracle tags on the parity, matrix, semantic,
small-step, builtin and bytestring-hash results, together with the exported
membership instruction traces. The retained aggregate behavior evidence and
its limitations are described in `membership-element-consistency.md`.

To rebuild the scoped fixture checks, from the repository root:

```sh
holbuild --max-heap 8000 -j2 build --skip-checkpoints --skip-proof-steps \
  --force=theory vyperMembershipParityTestTheory \
  vyperMembershipMatrixTestTheory vyperMembershipAuditTestTheory \
  membershipCheckerIntegrityTheory
```

These checks establish finite parity and the stated semantic boundaries.
They do not prove universal end-to-end compiler correctness or Keccak
injectivity. General pre-existing lowering admissions are outside this check.
