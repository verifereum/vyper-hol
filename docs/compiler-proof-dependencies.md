# Compiler proof dependencies

Milestone 1 boundary at `e4cb0914`, audited 2026-10-09. The current
`vyper_call_correct` theorem takes a
[fixed storage region set](compiler-correctness-specification.md#fixed-storage-regions).
This is a dependency/assumption inventory, **not a fully verified compiler**.
The [dated audit](compiler-proof-status-2026-10-09.md) contains the entire public
schema, exact saved-object receipts and historical evidence identities.
TASK060 final merged validation is **complete**; see the
[exit report](compiler-proof-milestone-1-exit-2026-10-09.md).
The initial documentation audit did not rerun builds/tests.

Related: [specification](compiler-correctness-specification.md#calls-and-nested-contexts),
[definition parity](compiler-definition-parity.md),
[roadmap](compiler-proof-roadmap.md), [status pointer](compiler-proof-status.md).
The roadmap includes future work, not additional current proved contracts.

## Classification of hypotheses

- **environmental** — execution setting, not established by the compiler;
- **boundary** — input/compiler-run validity at the formal boundary;
- **produced** — established by a named stage/structural theorem;
- **preserved** — assumed at input and proved to survive transformation;
- **consumed** — required here, with its upstream producer identified.

A producer may be **ADMITTED**. Empty `Thm.hyp` means a closed kernel statement,
not freedom from admission tags. Theory ancestry/imports are not the same as
logical proof dependencies. Compilation success, syntactic fixture membership
and exact bytecode equality are not semantic stage correctness.

## Exact O1 runtime dependency graph

This is the Milestone 1 graph, for the identity finalizer `K SOME`. Today's
`vyper_call_correct` has eight public premises (table below); its proof cases
on calldata dispatch and then on the finalizer (`vyper_call_correct_guarded`,
`vyper_call_correct_dispatched`).

```text
compile_vyper (K SOME) succeeds
  -> L1 actual rpolicy/raw unit/O1 out/assembly prog/plan cp
       runtime_bc = assemble prog (actual data segment/code-end header)

supported_program -> S2 raw source-unit shape -> S6 output shape
call_state_rel + shared entry_venom_state -> L6/L7/L8 initial relations
source typing/storage + valid ABI call + outcome guards -> S1

non-exempt branch:
  S3 raw memory -> S4 forward O1 simulation
  S5 chooses Inv, output memory and reachability
  L2/L4/L5 + S5 memory -> structural codegen context obligations
  S7, using SAME Inv -> frame-aware EVM correspondence/resource alternatives

clean generic e2e_vyper_to_evm (explicit stage premises, zero admission leaves)
  -> vyper_call_correct (seven public premises at Milestone 1; inherits exactly S1-S7)
exempt branch: actual total run + exact decoder exemption, not invented safety
```

The compiler is the actual `run_venom_pipeline ... o1_pipeline_spec`, not an
arbitrary mandatory-pass surrogate, a legacy pass pipeline, or an O2/O3 claim.
The finalizer `fin` is in `accepted_finalizers`: identity `K SOME` or
`asm_opt_finalizer`. No `finalizer_correct` assumption remains.
Memory/shape/policy/labels/initial state are **not extra public hypotheses**.

## All public hypotheses and producers

The call boundary below has no separate immutable restriction. The
[dated audit](compiler-proof-status-2026-10-09.md#public-runtime-theorem)
preserves its historical schema.

| Hypothesis | Class | Current producer / absence |
|---|---|---|
| `fin IN accepted_finalizers`, `compile_vyper fin policy tops = SOME (deploy_bc,runtime_bc)` | boundary | Caller supplies success; L1 (`compile_vyper_runtime_phases`, `K SOME`) or `compile_vyper_runtime_phases_asm_opt` extracts raw phases and the exact assembled runtime bytes (`assemble prog'` of the optimized `prog'` for `asm_opt_finalizer`). No universal success producer. |
| `supported_program tops` | computational boundary | Plain EVAL on concrete `tops`; exact whitelist on `tops` alone. No universal membership, typing or semantic correctness producer. |
| `source_typing_ok tops am tx` | boundary + environmental | Checker artifact; partial `load_contract_establishes_checked_contract_runtime_ready`, `load_contract_establishes_machine_well_typed`, `checked_call_external_preserves_machine_well_typed`. No complete arbitrary-environment producer. |
| `storage_ok H am tx`, `call_within H tops am tx es` | environmental storage horizon | The caller fixes the regions `H`. When calldata dispatch selects a function and the frame is not resource-starved, `call_result_rel H` gives `storage_ok H` again after the call. No producer of `call_within`, and no deployment/transaction producer of `storage_ok`. |
| `call_state_rel tops runtime_bc am tx es` | environmental | No general producer or satisfiability theorem. L6/L8 **consume**, not produce, it; transaction corollary deferred to Milestone 7. |
| `LENGTH (call_trace es) < 2 ** 64` | environmental call-count bound | No producer. The frame's observed calls, computed precompiles included, number fewer than `2 ** 64`. |

The [partial-producer detail](compiler-proof-status-2026-10-09.md#what-partial-producers-actually-establish)
is part of this inventory: runtime readiness requires installed exact sources
and ready immutables; deployment assumes initial typing, both checks/context/
constants setup; call machine preservation assumes `checked_external_call_inputs_ready`.
Storage preservation consumes `contract_storage_well_formed`, protected-call
(`protected_storage_calls_preserve`) and oracle-storage (`oracle_storage_ok`)
premises, or, in its finite-horizon form (`call_external_storage_well_formed_on`,
`load_contract_storage_well_formed_on`), a `valid_horizon` over the actual
trace. These are not universal producers.

`call_outcomes_ok`, which `call_state_rel_call_outcomes_ok` derives from
`call_state_rel`, requires return-data length `< 2**256` and
`accounts_runtime_well_typed co_accounts` on every record, including failed and
static outcomes. `call_storage_ok` for runtime calls and `deploy_storage_ok`
for constructors supply the separate finite-trace storage obligations over
the regions and backends observed for the chosen gas readings.

## S1–S7: current admitted producers

Each row except S1 is **ADMITTED**, a final statement/memo with future
proof owner. S1 is proved from the entry bridge, `body_stmts_sim` and the
halt bridge, and rests on the named admissions listed in
`lowering/loweringRuntimeCorrectScript.sml` and on `body_stmts_sim`'s case
admissions. Generic composition and each L1–L13 have none. See [source owners and receipt](compiler-proof-status-2026-10-09.md#built-logical-admission-path).

| ID | Saved export | Consumes / produces | Future owner |
|---|---|---|---|
| S1 | `loweringRuntimeCorrect.lower_vyper_runtime_unit_correct` | raw lowering, boundary/entry facts -> terminating source-unit execution | Milestone 6 |
| S2 | `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok` | lowering + supported syntax -> `o1_source_unit_ok` | Milestone 5 |
| S3 | `loweringMemCorrect.lower_vyper_runtime_unit_memory_ok` | S1 boundary + non-exemption + no `DALLOCA` -> `raw_unit_memory_ok` | Milestone 5 |
| S3d | `loweringMemCorrect.lower_vyper_runtime_unit_dload_offset_ok` | S1 boundary + `code_layout_valid` + non-exemption -> `mem_inv dload_offset_ok` (DLOAD/DLOADBYTES offsets plus the code prefix stay below 2^256) | Milestone 5 |
| S4 | `o1PipelineCorrect.run_venom_pipeline_correct` | exact O1 success, raw shape/entry/memory, `o1_run_state_ok` (incl. `code_layout_valid`), DLOAD offset bound (`mem_inv dload_offset_ok`) -> forward simulation up to any well-formed dead-byte set `D` (`ctx_sim D`, `dead_wf D`) | Milestone 3 |
| S5 | `o1PipelineCorrect.o1_pipeline_memory_obligations` | O1, generated plan, raw shape/entry/memory -> existential `Inv`, output memory/reachability | Milestone 5 |
| S6 | `o1PipelineCorrect.run_venom_pipeline_output_shape` | exact O1 + raw source-unit shape -> output `unit_shape_ok` | Milestone 3 |
| S7 | `codegenCorrectness.codegen_correct` | assembly/plan, context/reachability, shape and initial relation -> run_call/frame/resource correspondence | Milestones 2.1 and 4 |

Pipeline result transport is success-observable preserving, forward and
terminating; failed-run return bytes/general abort kind/requests may differ.
Generated plan layout does not prove spill safety. Empty entry memory does not
prove raw memory validity. Return-address uses and labels are constrained by
output shape. The result relation `call_result_rel` ties source gas
observations to the EVM's readings through `gas_readings_rel`.

## Clean producers and composition

Actual qualified L1–L13 names, owners and conclusions are in the
[clean structural table](compiler-proof-status-2026-10-09.md#clean-structural-producers-l1l13).
They are separately saved Hyp0/no-axiom/no-admission objects. In particular:

- L1 `e2eProducers.compile_vyper_runtime_phases` extracts the actual phases.
- L5 `e2eProducers.o1_pipeline_codegen_obligations` still **consumes** S5's
  memory obligation; L2 layout and checked driver facts supply structural parts.
- L6/L7/L8 use one concrete `e2eEntry.entry_venom_state`; labels are actual
  `compute_label_offsets prog`, FMP is the generated plan's value.
- L9 `frameOutcome.frame_outcome_single_frame_run` consumes `frame_outcome`;
  it is not a derivation of that relation for arbitrary EVM runs.
- `e2eCorrectness.e2e_vyper_to_evm` is clean generic composition with explicit
  stage contracts; `vyper_call_correct` closes them with admitted S1–S7.

TASK056 full saved logical closures: top378/generic30 recorded nodes, no legacy,
deployment or function-simulation dependencies. Source admission count is
**130→128**, removing exactly the local `evm_correspondence_to_call_result`
and `codegen_correct_legacy` sites; no new site. This is a named delta, not a
proof of remaining stages or a plan-count substitution.

## Calls, resources and scope

The [entry/oracle/result specification](compiler-proof-status-2026-10-09.md#entry-oracle-and-observations)
uses fresh nonstatic head frames with arbitrary parents, live post-transfer
accounts, exact source installation/layouts, code/parse and message/transaction/
block ties. `run_call` stops when our frame ends; parent return/revert/short
output-copy behavior is specified by `frame_outcome`, not by a whole-transaction
claim. Source oracle `SOME` and Venom/assembly calls take complete outcomes;
computed value-zero precompiles 1/2/6/7 consume the next outcome and use its
success flag when the computed input is valid. No callee source correctness is
presumed or proved.

Success relates `tx_return_bytes`, accounts after EVM pending deletions,
transient storage modulo dead target storage, logs and the full request
list (computed precompiles included) via `request_agree`. A source halt relates the same effects (`effects_agree`) with empty output. Requests and these effects are compared only on success or halt, never on failure; leftover outcomes are not final
observations. Non-exempt source failure requires target failure, without
revert-data/reason/general-kind equality. The sole exemption is exact
`RuntimeError "abi_decode invalid"` with a dynamic target occurring in a function
body (including a return rejection producing that same message); not arbitrary
`ReturnReject`, static-only decoding or conversion failure.

The resource alternative is frame OutOfGas/StackOverflow, not an existential gas
threshold. Entry `cc_gas=0`; Venom GAS consumes the frame's gas readings,
returning zero on exhaustion.
There is no msg.gas guarantee beyond `gas_readings_rel` and no caller-read
gas-reading correspondence; the result relation ties source gas observations to the frame's EVM gas readings only through `gas_readings_rel (gas_readings es)`: it fixes some slots of the source's gas observations so that the fixed (`SOME`) slots together with the unused readings are a permutation of `gas_readings es`, and the result must hold for every value in an unfixed (`NONE`) slot and every appended tail, which the EVM readings do not constrain. For `gas=`, only the forwarded gas operand is related: on success or halt `request_agree` requires it to equal an explicit source `gas=` value; a `send` without `gas=` must forward 0; other calls without `gas=` and the gas the callee actually receives are unconstrained. Combined environmental satisfiability and transaction/callee
producers remain Milestone 7 work.

## Deployment, function simulation and retired contracts

`e2eDeployCorrectness.e2e_deploy_correctness` is a meaningful **ADMITTED** single-frame
creation statement (Milestone 6 item7), not the old proved `T` placeholder.
It requires Call-free constructor bodies, canonical arguments, actual deployment
typing/storage/pre-constant readiness, an uninstalled source target and an empty
target account in `es.originalAccounts`; success
compares returned/installed `runtime_bc ++ section` satisfying `immutables_section_rel`,
accounts modulo target code and dead storage, transient storage modulo dead
target storage, and logs.
`venomToAsmProps.gen_fn_simulation` is separately **ADMITTED**, Milestone 4.2,
with internal-return/frame relations. Both are **off the runtime call path**.

The [completed retirement ledger](../lowering/e2eLegacy.md) maps all21 obsolete
definitions/all14 claims to the new API, preserves exact original proof
provenance and records export absence. No live compatibility aliases remain.
Old counterexamples/proof history are retained in the
[historical audit](compiler-proof-status-2026-09-28.md), not relabeled current.
The four original clean structural public schemas remain preserved; their
names/receipts are in the dated audit, not replacement correctness certificates.

## Validation boundary

Reuse only identified valid evidence at its scope. TASK034's completed primary
source/generated non-parity checkpoint and TASK022 membership gate retain their
own revisions. TASK056's current eight-root primary gate and logical audits are
local/targeted, not full final integration. TASK065 strict101/exact-byte proof is
**historical only**. The subsequent [TASK060 exit report](compiler-proof-milestone-1-exit-2026-10-09.md)
certifies the final project/optional/module closure, all selected generated
results, all101 membership/strict bytecode objects, independent bytes and final
documentation/dependency/admission checks. Later milestones must still prove
the admitted stages and environment producers. See [evidence provenance](compiler-proof-status-2026-10-09.md#evidence-provenance-and-remaining-checkpoint-debt).
