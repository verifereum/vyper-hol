# Compiler correctness roadmap

This document is the plan for closing the end-to-end compiler correctness proof.
It is ordered by dependency, not calendar time. Revised **2026-10-09** against
accepted TASK057 base `e88dae75` (TASK056 implementation at `e4cb0914`).
This is a documentation-only handoff, not a new proof/test certification.
The 2026-09-28 roadmap recorded the O1/parity/Osaka state; its gas-number
proposal of 2026-09-29 is superseded below, not retrospectively implemented.
The earlier version is archived as
[`archive/compiler-proof-roadmap-2026-09-25.md`](archive/compiler-proof-roadmap-2026-09-25.md).

Related documents:

- [`compiler-proof-status.md`](compiler-proof-status.md): latest audit, with every cheat classified by relevance
- [`compiler-correctness-specification.md`](compiler-correctness-specification.md): theorem boundary and scope
- [`compiler-proof-dependencies.md`](compiler-proof-dependencies.md): cross-stage invariant structure
- [`compiler-definition-parity.md`](compiler-definition-parity.md): parity with `VYPER_PIN`
- [`bytecode-fixture-coverage.md`](bytecode-fixture-coverage.md): differential bytecode evidence
- [`compiler-proof-drafts-and-counterexamples.md`](compiler-proof-drafts-and-counterexamples.md): known false statements

## Where we are

The call headline is documented in the
[fixed-storage call specification](compiler-correctness-specification.md#fixed-storage-regions).

**Milestone 1 statement infrastructure (2026-10-09):**

- The target is actual O1 `compile_vyper (K SOME)`, using
  `run_venom_pipeline (K T) (K T) (K T) ... o1_pipeline_spec`, not a legacy
  mandatory-pass surrogate. Successful compilation is a boundary input;
  identity finalization yields `runtime_bc = assemble prog` via L1.
- `e2eCorrectness.vyper_call_correct` has the exact
  [Milestone 1 call schema](compiler-correctness-specification.md#milestone-1-runtime-contract-2026-10-09).
  At Milestone 1 its composition proof inherited **exactly seven ADMITTED
  stage leaves**; all seven stages are proved now. The old configured `e2e_vyper_to_evm_O1` export is retired.
- `e2eCorrectness.e2e_vyper_to_evm` is **proved generic composition** with
  explicit stage contracts; each L1–L13 structural producer is proved with
  zero admission leaves. They do not prove the stages they compose.
- The outcome oracle, live fresh-frame relations, corrected source/Venom/asm
  semantics and completed [retirement ledger](../lowering/e2eLegacy.md) are
  implemented. The old false statements remain historical counterexamples,
  not current certificates or hidden compatibility bridges.
- 101 whitelist membership proofs and historical strict101/exact-byte evidence
  have identified scopes. Neither is universal compile success or semantic
  correctness. The subsequent [TASK060 exit verification](compiler-proof-milestone-1-exit-2026-10-09.md)
  also passed final merged validation; S1–S7 were still admitted then.

### Current stage contracts and proof owners

Names below are actual exports. All seven rows are proved, with no admission in
their closures. `vyper_call_correct`, `e2e_deploy_correctness` and S1 reach no
admitted lemma. `vyper_call_gas_sufficient` reaches only
`call_entry_reachable_create_size_ok` and `e2e_deploy_gas_sufficient` only
`deploy_entry_reachable_create_size_ok`
([e2eGasSufficient](../lowering/e2eGasSufficientScript.sml)): the two held
claims, marked `GATE_ADMISSION`, that, from the call or deploy entry, every
reachable creation instruction meets the init-code size check
`inst_create_size_ok`, blueprint forms included. The one other admitted
theorem, `function_inliner_correct`, lies under no top. The stage rows' exact
premises are in the linked owners and [dependency
inventory](compiler-proof-dependencies.md#s1s7-stage-producers).

| Stage | Actual export / owner | Contract | Owner milestone |
|---|---|---|---|
| S1 | `loweringRuntimeCorrect.lower_vyper_runtime_unit_correct` ([source](../lowering/loweringRuntimeCorrectScript.sml)) | Raw lowering + `supported_program` + `source_typing_ok` + `source_deployment_rel` + `valid_vyper_call` + `initial_venom_state_rel` + `outcomes_accounts_typed` + `DALLOCA` budget and free-memory-pointer headroom (`dalloca_fmp_headroom`) guards -> `source_unit_execution_correct`: for some gas marks, a raw exit related to the source result at every valid storage horizon, or a focus witness when storage is invalid for every gas tail appended to the readings the marks select or the source run is the same for every tail and exempt | 6 |
| S2 | `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok` ([source](../lowering/vyperLoweringCorrectScript.sml)) | Lowering + `check_contract F` + `raw_shape_free_program` -> `o1_source_unit_ok` | 5 |
| S3 | `loweringMemCorrect.lower_vyper_runtime_unit_memory_ok` ([source](../lowering/loweringMemCorrectScript.sml)) | Lowering + initial state + no `DALLOCA` + entry FMP floor + `__entry` lookup and entry label + memory-safe and pointer-safe entry runs at every fuel -> `raw_unit_memory_ok`, no function `fn_eom`, `fixed_region_reserved 0`, pointer discipline and taint bounds | 5 |
| S4 | `o1PipelineCorrect.run_venom_pipeline_correct` ([source](../venom/compiler/o1PipelineCorrectScript.sml)) | Actual O1 success + raw shape (`o1_source_unit_ok`, `unit_entry_no_params`, `unit_defs_reach_uses`, `unit_fmp_unsealed`) + `o1_run_state_ok` + reserved-region/EOM/FMP facts + `dead_wf D` -> an input state at which raw memory, pointer, taint and DLOAD bounds give forward simulation `ctx_sim D` and the output's `o1_lowered_inv` | 3 |
| S5 | `o1PipelineCorrect.o1_pipeline_memory_obligations` (same owner) | Generated plan for the O1 output + `o1_lowered_inv` of the output + matching initial FMP -> **one existential `Inv`** with output memory obligations/reachability | 5 |
| S6 | `o1PipelineCorrect.run_venom_pipeline_output_shape` (same owner) | Actual O1 success + `o1_source_unit_ok` + `unit_entry_no_params` + `unit_defs_reach_uses` + `unit_fmp_unsealed` -> `unit_shape_ok` | 3 |
| S7 | `codegenCorrectness.codegen_correct` ([source](../venom/codegen/codegenCorrectnessScript.sml)) | Generated plan/assembly + shape + context/reachability + initial frame relation -> actual `run_call`, resource alternatives or `venom_frame_rel` | 2.1 / 4 |

The top uses S1 even on exempt source executions. Only its non-exempt branch
needs S3/S4/S7 and memory/reachability facts at the concrete `Inv`
`raw_reachable vs0` (`vs0` the O1 output's entry state) rather than one the
caller supplies. On the ordinary path they have S5's form and come from
`e2eProducers.o1_pipeline_memory_obligations_raw`; on the static-abort path they
come from `abort_context_obligations_raw`, and their memory obligations exclude
the abort prefix (`codegen_memory_obligations_abort`). The S5 export itself is used by the
gas-sufficiency proofs. S2/S6 produce
shape. The call tops take the raw shape S4/S6 need from successful runtime
lowering and `check_contract F` (`lower_vyper_runtime_unit_checked_source_shape`):
`raw_shape_free_program` units use S2's helper
`lower_vyper_runtime_unit_source_unit_ok_checked` (the S2 export is its
corollary) with `lower_vyper_runtime_unit_o1_shape_extras`, and the rest (`raw_call` on `msg.data`,
`create_copy_of`, `create_from_blueprint`) use three proved shape cases.
The deploy tops use `checked_lower_vyper_deploy_unit_source_shape`, with three
matching proved deploy cases. On the ordinary path L5 consumes that memory fact; layout or empty
entry memory does not manufacture memory safety.

`venomToAsmProps.gen_fn_simulation` is proved (4.2); S7's `codegen_correct`
uses it through `codegenEntrySim.codegen_entry_asm_sim`.
**Off the runtime call path:** the separate deployment theorem
`e2eDeployCorrectness.e2e_deploy_correctness` is proved (6 item 7) and reaches
no admitted lemma. Current top/generic
logical closures contain neither it nor any retired API.

None of the four top theorems assumes the whitelist. `vyper_call_correct` and
`vyper_call_gas_sufficient` derive `supported_program` from `source_typing_ok`
and the `source_deployment_rel` inside `call_state_rel`
(`source_typing_ok_supported_program`); the deploy pair derives
`supported_program` and `supported_program_deploy` from `deploy_typing_ok` and
the `layouts_agree` inside `deploy_state_rel`
(`deploy_typing_ok_supported_programs`). Runtime lowering refuses an
unfolded `sha256` in external defaults (`external_defaults_no_sha256`).

**Named inventory, not forced plan arithmetic:** TASK056's source ledger is
**130 -> 128**, removing only the local
`e2eCorrectness.evm_correspondence_to_call_result` and
`codegenCorrectness.codegen_correct_legacy` admission sites. All other site
identities/multiplicities were preserved in the named ledgers
`/tmp/m1-056-sites-before.txt` / `/tmp/m1-056-sites-final.txt` (ephemeral receipts).
This docs task changes zero sites; it does not recount/certify admissions.
See the [dated inventory](compiler-proof-status-2026-10-09.md#off-the-runtime-call-path-retirement-and-proof-history).
At Milestone 1 the remaining problems were the seven stage proofs (all proved
since), old dispatched-pass gaps, and absent environmental
producers/satisfiability, not unfinished Milestone 1 statement edits.

## Principles

- **Repair statements before proving.** Independently check a known concrete
  counterexample before minimally repairing a false statement. Preserve the
  original statement/proof and show the replacement composes with its
  consumer; do not newly admit a formerly proved claim.
- **Prove what the compiler runs.** Theorems about legacy pass variants,
  `run_lowering_pair_compat`, or the old `venom_pipeline` count only once
  they are bridged to the dispatched definition.
- **Let run-time checks do the work.** `run_venom_pipeline` already checks
  `unit_wf`, `codegen_ready` and `reachable_fcg_acyclic`. Use those checks
  instead of proving structural preservation, unless a later semantic proof
  needs the fact at an intermediate stage.
- **Close general statements early.** State each theorem in its final,
  general form, and close it early with only named, narrowly scoped cheats
  for the cases not yet covered (see Milestone 2). Do not prove results
  restricted to a class of programs.
- **Keep the inventory honest.** Retire obsolete APIs with preserved proof
  provenance, not silent deletion or aliases. Record missing theorems alongside
  admissions; imports/build ancestors are not logical proof dependencies.

## Milestone 1: A true and complete top-level statement

Statement/composition goal: every top premise has a boundary/environment
classification or a named producer, whose status is explicit. Accepted local
infrastructure has met that statement goal; final merged validation remains
TASK060. S1–S7 are believed proof targets, **not truth certificates**. No
satisfiable successful-compilation witness is manufactured by this roadmap.

### 1.1 Call boundary, external calls and gas

**Historical decision:** the 2026-09-29 discussion following #98 proposed
source gas numbers and concrete atomic callee execution. D1 of the 2026-10-01
Milestone 1 plan replaces it with **full call outcomes**. Fixing gas alone did
not align warm addresses, depth, stipend, balance checks, precompile dispatch,
`toDelete` or `msdomain`. The old proposal is history, not an active TODO.

**Implemented boundary:** Verifereum's `run_call` stops at our fresh nonstatic
head frame, with arbitrary caller frames below it; it does not finish their
transaction. Live post-transfer accounts, exact installed singleton source and
layouts, installed frame code/parser and message/transaction/block ties are in
`e2eDefs.call_state_rel`. `frameOutcome.frame_outcome` describes success/failure,
return bytes/logs and the parent's success word, PC, short memory splice and
rollback. L9's proved single-frame bridge **consumes** `frame_outcome`; deriving
it from a general well-formed frame run is still a 2.1 obligation.

[extCallOracle](../extCallOracleScript.sml) defines the actual records:

| Record | Fields |
|---|---|
| `call_request` | `cr_kind`, `cr_gas`, `cr_data_len`, `cr_target`, `cr_value`, `cr_data`, `cr_static`, **live pre-call** `cr_accounts`, `cr_tStorage` |
| `call_outcome` | `co_created`, `co_success`, `co_returnData`, **post-call accounts including balance/code/storage** `co_accounts`, `co_tStorage`, `co_logs`, `co_toDelete` |

One [source evaluator](../semantics/vyperInterpreterScript.sml) has two modes:
`call_external NONE` concretely runs callees; `call_external (SOME os)` takes
outcomes. Arbitrary SOME lists use this same evaluator, not a theorem-only
interpreter. Runtime theorem mode uses
`call_external (SOME (MAP SND (call_trace es))) gobs am tx` for source gas
observations `gobs`. When calldata dispatch selects a function and the frame
is not resource-starved, `vyper_call_correct`'s `call_result_rel` relates
them, at `tx` with that function and its arguments, to the EVM's readings
`gas_readings es` through `gas_readings_rel` (below), which picks
existentially which slots of `gobs` the readings fill, leaving the other
readings unused, then covers every `gobs` that matches them, with any tail.
Venom and [assembly](../venom/codegen/defs/asmSemScript.sml) CALL/STATICCALL also
use `take_outcome`, `record_request`, `adopt_outcome`. A call that finds the
outcome list empty stops the run: Venom aborts (`ExHalt_abort`), assembly
faults (`AsmFault`) and the source raises an error. Failed/static calls adopt
no accounts/transient/log effects; successful nonstatic calls adopt the
supplied accounts, transient storage, logs and deletions, except computed
calls (below), which take only the outcome's success. Source
`take_call_outcome` checks successful nonstatic account balance/code bounds;
this is **not a storage validator**. The public `call_outcomes_ok` additionally
requires bounded return data and runtime well-typed accounts for every record,
including failed and static ones. Storage validity is separate.
`vyper_call_correct` fixes the storage regions: `storage_ok H` asks them to be
consistent, their locks separated and decoding at the entry state, and
`call_within H` checks, when calldata dispatch selects a function, every gas
filling's source storage observations against them (`storage_observations_ok`).
e2eDefs's finite trace guard `call_storage_ok` is the per-gas-filling form
over the trace's own horizon: the roots and lock slots the call's source
storage trace observes are in range, its regions are consistent, their locks
separated, and they decode at the entry state and in every adopted backend.
`call_state_rel_call_outcomes_ok` produces `call_outcomes_ok` from the EVM
call trace. `closed_world_call_outcomes_ok` produces `call_storage_ok` under
its closed-world premises, for the gas observations related to the EVM
readings, unless the frame is resource-starved. No arbitrary-callee or
source-executed-callee producer of the storage guards exists yet.

**Deterministic observer, not a freely chosen oracle.**
[callTrace](../venom/codegen/frame/callTraceScript.sml) defines `frame_obs_tr`
with the `run_call_tr` gas-decrease measure. `trace_obs` has entries, readings
and a pending `(request, pre-call log count, pre-call deletion count)`. `observe` records only our frame:

| Step shape | Actual observer action |
|---|---|
| Our frame executes GAS and continues at the same depth | append the post-step top stack word to `readings` |
| CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 with enough stack completes at our depth | append `request_of` / `outcome_of` immediately |
| It pushes a callee | save request and our log/deletion counts; descendant calls do not overwrite it |
| That callee returns to our depth | append the pending pair and clear pending |
| Our frame faults/pops, or an unobserved instruction/descendant step occurs | no new entry |

`call_trace es` includes value-zero computed precompiles, and
`call_requests es` is `MAP FST (call_trace es)`: every entry's request, those
included. `gas_readings es` is a separate
frame-local list for assembly initialization, **not a source gas-number
oracle**. The observer is total/deterministic; trace decomposition and semantic
correctness are not proved by totality and remain 2.1 work. CALLCODE is not observed;
DELEGATECALL and CREATE/CREATE2 are observed and inside S7's `unit_shape_ok`;
no correctness of the delegated or created callee is claimed.

**Computed calls:** value zero to addresses 1/2/6/7 uses `precompile_result`
(ecrecover/SHA256/ecadd/ecmul) for its return data, takes its success from
the next outcome (the EVM can starve it of gas), records its request like
any call and otherwise preserves state. The source's sha256/ecrecover/ecadd/ecmul builtins take that
outcome too. Invalid EC input gives failure; invalid ecrecover is a valid
successful empty result. Nonzero value or another precompile is ordinary.

**Gas and observations:** entry `cc_gas = 0` and `vs_gas_readings = gas_readings es`.
Venom GAS and assembly GAS consume frame-local readings, returning zero on
exhaustion. `unitShapeDefs.opaque_use_ok` restricts return-address uses.
`gas_readings_rel` constrains source gas fillings using the EVM readings
and allows slots with no corresponding reading. The
[fixed-storage call theorem](compiler-correctness-specification.md#fixed-storage-regions)
gives a `run_call` result that either is frame-resource-starved or satisfies
`calldata_result_rel H`, including the unmatched-calldata case.

The companion `vyper_call_gas_sufficient`
(`lowering/e2eGasSufficientTopScript.sml`) gives a threshold `g` such that
adding any `g' >= g` gas to the frame yields a run. When
`calldata_dispatch` selects a source call, the gas guarantee requires the
raised-gas trace length to be below `2 ** 64`, `call_storage_ok` for every
gas filling of its outcomes, and `~gas_source_exempt` for every source
observation of that call. Under those conditions, an OutOfGas run reaches
a `RETURNDATACOPY` instruction (`frame_inst_at`). The same OutOfGas
conclusion applies to unmatched calldata.
The identity case composes the stage bounds S1b
(`lower_vyper_runtime_unit_run_bounded`), S6b
(`run_venom_pipeline_run_bounded`) and S7g (`codegen_gas_sufficient`). The deploy twin
`e2e_deploy_gas_sufficient` uses the deploy unit's fuel bound
(`deploy_unit_fns_fuel_stable` with `run_context_uniform_fuel`),
`run_venom_pipeline_run_bounded_raw` and the proved S7g-d
`deploy_frame_gas_sufficient`. Its proof uses `compile_vyper_runtime_not_ef`
to derive that the runtime bytecode does not start with `0xEF` from successful
compilation with an accepted finalizer. Under `deploy_storage_ok` for every
gas filling, no exempt source observation and fewer than 2⁶⁴ trace entries on
the raised-gas run, its OutOfGas conclusion allows oversized deposited code or
a reached `RETURNDATACOPY`;
its per-finalizer cases (`e2e_deploy_gas_sufficient_identity`,
`e2e_deploy_gas_sufficient_asm_opt`) allow the same two alternatives.
Each companion rests on one admitted lemma, its entry's held create-size
claim (`call_entry_reachable_create_size_ok`,
`deploy_entry_reachable_create_size_ok`, marked `GATE_ADMISSION`); no other
admitted theorem lies under either, assembly-optimizer cases included. The
correctness tops reach neither.

On success the result relates `tx_return_bytes`, accounts after EVM pending
deletions and transient storage modulo dead target storage, ordered concrete logs
and the full request list `call_requests es` (every trace entry's request,
computed precompiles included) via `request_agree`. A source halt relates the
same logs, accounts, transient storage and requests (`effects_agree`) with empty output.
Failed-run requests, leftover terminal outcomes, revert data/reason and general
abort kind are not compared, except that calldata with `calldata_dispatch` `NONE`
requires a raised `Reverted` outcome with empty output outside resource starvation. `unspecified_behaviour_exempt` covers exact
`RuntimeError "abi_decode invalid"` with a dynamic ABI target occurring in a
function body; it may also cover a callee-return rejection with that exact
message, not arbitrary ReturnReject/conversion/static decode failure.
Callee/reentrant execution is absorbed into an outcome, not certified as
source-equivalent. Full nested-run decomposition and repeated-entry/transaction
corollaries remain Milestone 7.

### Decision ledger D1–D31

This table retains the 2026-10-01 plan's decision keys. Restrictions it
attributes to the whitelist are the Milestone 1 gate's: the current gate
accepts what `check_contract` accepts, and what remains is what the
lowering refuses and the two held create-size claims under the gas
companions. “Implemented” means
actual definitions/statements, **not stage proofs**. “Deviation/limit” is
explicit; no intended producer is reported as proved merely because it was
planned. Source owners below are durable; private PLAN line numbers are not.

| Key | Decision / rejected alternative | Current implementation and explicit deviation or limit | Future owner |
|---|---|---|---|
| D1 | Full outcome oracle; requests on success or halt | `extCallOracle` records and source SOME/Venom/asm call adoption. `call_result_rel_at` compares the full request list on success and halt via `effects_agree` and `request_agree`. The observer records the message-call gas operand in `cr_gas`, and `request_agree` matches it to the explicit source `gas=` value when present. | 2.1 trace / 7 callee producer |
| D2 | Resource disjunction, not existential sufficient gas | `frame_resource_starved` is OutOfGas/StackOverflow; a starved computed precompile is an oracle outcome. The gas bound is the separate companion `vyper_call_gas_sufficient`. | 2.1 / 4 |
| D3 | Frame-local GAS readings | Venom `exec_gas` and `asm_gas` consume readings, zero on exhaustion. The entry uses `gas_readings es`, and `call_result_rel H` checks all source gas fillings allowed by `gas_readings_rel`. | 2.1 / 4.2 |
| D4 | Compute value-zero precompiles 1/2/6/7's data, take their success from the oracle | `precompile_result`, `take_outcome`, `precompile_call_success`, every request recorded (`record_request`, `call_requests`); helper purity is proved, EVM purity bridge is deferred. | 2.1 |
| D5 | One evaluator NONE/SOME, not duplicate evaluator or unchecked accounts | Source `evaluation_state.outcomes/requests`, `take_call_outcome` account guard; full triples at call/deploy entry, two-argument initializer retained. Existing storage/type proof guards remain conditional; no universal storage validator. | 6 / 7 |
| D6 | SOME send requests a real call outcome, not pure transfer | Source Send uses empty-data nonstatic request and requires success; NONE retains concrete transfer behavior. | 6 |
| D7 | Restrict ExtCall syntax, not reorder source evaluation | `supportedExprs`/`supportedExprForms`: effect-free operands, word arguments/returns, exact interface/count, distinct `value=`/`gas=`/`default_return_value=` operands evaluated in source order (#553); SOME code check follows return-kind policy and `skip_contract_check`. `NoneT` ExtCall was **not admitted** at Milestone 1; the current gate admits a `NoneT` external return (`supported_external_return_type`). | 6 |
| D8 | Runtime failure requires Abort/failing frame, not anything/fuel0 | `external_call_result_rel` rejects OK/IntRet and other Errors, relates a failed external call's `RevertData` to a Revert abort, and requires terminating run; `call_result_rel_at` failure clause. TypeError is excluded by typing, not treated as source success. | 6 |
| D9 | Exact unspecified-behaviour exemptions, not weakened source checks | `unspecified_behaviour_exempt`, `occurs_abi_decode_target` inspect function bodies for dynamic decoding. Exact decode message also admits matching return rejection in such a program; not arbitrary ReturnReject. | 6 |
| D10 | Typing separate from plain-EVAL syntax | `source_typing_ok` contains checker acceptance, typed constant cells, machine and tx typing; `supported_program` depends on tops alone and is no longer a premise: the tops derive it from the checker acceptance and `layouts_agree` (`check_contract_supported_program`), which `source_deployment_rel` supplies for calls and `deploy_state_rel` for deployment; for the deploy pair `deploy_typing_ok` supplies both `check_contract F` and `check_contract T` (`deploy_typing_ok_supported_programs`). Partial readiness producers are not the whole premise. | 7 |
| D11 | Whitelist, not open-ended exclusions | `supportedProgram` combines headers/names/body predicates; 101 named fixture membership proofs. The whitelist has since been widened to what `check_contract` accepts and is derived, not assumed, by the tops; forms it newly accepts are proved, bar the two held create-size claims under the gas companions. No universal compile-success witness. | 6 / 7 |
| D12 | Ten source/type corrections, not remove fixtures | Invalid EC RuntimeError; Pop length-only storage update; empty codehash zero; decimal bound-before-truncate; bytes->address/decimal/narrow-zero-tail conversions; UnsafeDiv0 zero; minimum decimal Mul; abi_encode size rule. Actual owners `vyperContext`, `vyperState`, `vyperValueOperation`, `vyperTypeSystem`; historical source checkpoint retained. | 6 comparison proof |
| D13 | Literal endpoint range checks + allocation-budget compiler check | `stmtLowering` tests both literal endpoints; five fixture bounds corrected historically. `vyperCompiler.lowering_context_ok` checks `unit_alloca_budget < dimword(:256)`. This is not a proof that every raw access is valid. | 5 / 6 |
| D14 | STOP clears data, empty setup_callee accepted, CALL/STATICCALL outcomes | `venomExecSemantics` implemented; DELEGATECALL takes its outcome from the oracle too. DELEGATECALL/CREATE/CREATE2 are inside `unit_shape_ok` (`inst_shape_ok` excludes only `DJMP` and `OFFSET`); the delegated or created callee is not oracle-certified. | 2.1 / 4 |
| D15 | Exclude static entry, not change write effects | `call_state_rel`/`initial_ctx_rel` nonstatic; outgoing STATICCALL is allowed. No static-entry correctness claim. | 7 generalization |
| D16 | Runtime immutables without a separate exclusion | The call theorem carries no separate immutable restriction. `call_state_rel` still requires frame code `runtime_bc ++ section` with `immutables_section_rel` for the target's immutables, and the live target account's code to equal the frame code; source installation is exact. Deployment remains separate. | 6 item7 |
| D17 | Forward success/weak abort transport, not observable_equiv for aborts | `unitTransformDefs.unit_result_rel`: Halt observables; Abort requires only REVERT stays REVERT. Failure returndata/kind/requests may differ. S4 proved, on `ctx_sim`'s `dead_result_rel`, which also lets Halt observables differ at dead bytes. | 3 |
| D18 | S6 output shape, not new compiler final-hook check | S6 proved; existing literal O1 hooks unchanged. Raw-only restrictions not required of output. | 3 |
| D19 | Syntax memory restrictions + raw memory contract | `raw_unit_memory_ok` is the raw memory contract at actual sites, and S3 produces it. S3/S5 proved; empty memory is not a producer. | 5 |
| D20 | Reachability at visited states, not unincremented results | `enters_block`, `fn_entry_inv`, `reachability_closed`, `codegen_reachability_package` include post-PHI, incremented continuations and INVOKE entries. Definitions are not a reachability proof. | 5 |
| D21 | `tx_return_bytes` | Raw-return functions use `raw_return_bytes`; otherwise `return_bytes` is empty for `NoneT` and uses a singleton tuple iff `needs_external_call_wrap`. | 6 |
| D22 | Actual entry transfer/block/code/log/layout guards | `call_state_rel` uses LIVE post-transfer accounts, block window/nonzero bounds, <=24576 bytes, empty logs and declared slots/source installation. Satisfiability not established. | 7 |
| D23 | Encoding wf only; remove positive-size hypothesis | `asm_encoding_wf` replaces `asm_wf` in encoding/step consumers; zero-size reverse lookup repaired. **Still absent:** general producer for actual generated output. | 2.1 |
| D24 | Reserved-label exclusions | `reserved_label`, `unit_shape_ok`, supported internal-name rules; S6 must produce shape, not arbitrary label-map assumptions. | 3 |
| D25 | Exact External call/count/binding; no fallback/defaults | `valid_vyper_call` implemented via real lookup; no general producer. `vyper_call_correct` covers fallback invocation: unmatched calldata dispatches to a declared `__default__` (`calldata_dispatch`), and `calldata_result_rel` covers that call. | 7 |
| D26 | Initial and outcome storage validity | `vyper_call_correct` takes fixed regions that decode at the entry state (`storage_ok H`) and against which, when calldata dispatch selects a function, every gas filling's source storage observations are checked (`call_within H`, `storage_observations_ok`); `call_storage_ok` is the per-gas-filling guard over the trace's own horizon, which decodes at the entry state and in every adopted backend; `call_outcomes_ok` holds only return-data and account bounds. Account/code guard alone is insufficient. The storage guards have no producer for arbitrary EVM callees; `closed_world_call_outcomes_ok` gives `call_storage_ok` only under its closed-world premises, for the gas observations related to the EVM readings, unless the frame is resource-starved. | 7 |
| D27 | Preserve/re-prove existing true claims | Completed retirement ledger preserves proof text/Git identities and four structural APIs. **Clarification:** D30's unused false claims retire without same-name replacements. The creation-frame theorem was introduced as a separate statement and has since been proved. | every proof owner |
| D28 | Meaningful single-frame deployment, not nested creation | `e2e_deploy_correctness` is proved, reaching no admitted lemma, for canonical args, checked deployment and runtime artifacts (pre-constant readiness follows from them), an uninstalled source target and an empty target account in `es.originalAccounts`. Constructors may make supported calls and take outcomes from their creation frame's trace. | 6 item7 |
| D29 | Retire unused codegen_fn_correct; frame-aware gen_fn_simulation | Actual entry/IntRet/return relations and concrete maps; proved; S7's `codegen_correct` uses it. This intentionally differs from old roadmap “restate codegen_fn_correct”. | 4.2 |
| D30 | Fresh output labels proved; unused false local claims retired | `fresh_label_output_inj` / output-state `fresh_label_produces_external` proved. Assign/zero-pad/generate-runtime correctness claims retired with provenance, not rewritten under the same names; Assign belongs to statement induction, runtime to S1. | 6 |
| D31 | Do not claim call_state_rel satisfiable in Milestone1 | No general producer or satisfiability theorem; focused checks are not a compiled-program witness. Top-level transaction construction is explicitly future work. | 7 |

D3's GAS restriction, D16's installed code/source boundary, D27/D30's retirement
semantics, and D28's deployment refinement are implementation qualifications,
not guesses about future proofs. The old roadmap's three gas/call/GAS “scoped
cheats” recipe is superseded by the outcome/opacity handoff in 2.1. No new stage
or satisfiability proof is silently added to Milestone 1.

### 1.2 Codegen statement

S7 now uses actual plan/program maps, `unit_shape_ok`,
`codegen_context_obligations`, corrected `codegen_reachability_package` and
`initial_ctx_rel` (live state, nonstatic wf/Collect frame, initial FMP/token,
assembled code/parser, concrete labels/outcomes). Its conclusion is
`run_call` plus the resource alternative or `venom_frame_rel`.
No sufficient-gas assumption remains. `codegen_fn_correct` is retired;
`gen_fn_simulation` has actual entry/return relations and an `IntRet` clause,
and is proved (4.2). Existing bridges are not trace-aware S7 proofs.

### 1.3 Lowering statement and the result relation

S1 is actual `lower_vyper_runtime_unit_correct`, replacing the retired
`vyper_to_venom_correct`. It consumes `supported_program`, `source_typing_ok`,
source deployment, exact valid call, `initial_venom_state_rel`, typed outcome
accounts and, for units with `DALLOCA`, allocation-budget and free-memory-pointer headroom (`dalloca_fmp_headroom`) guards. Unless storage is invalid for every gas tail appended to the readings its gas marks select, or
the source run is the same for every tail and source-exempt (it gives a focus
witness then), the raw run must reach an exit related to the source result at
every valid storage horizon; runtime
failure is Abort, not Error/fuel0. Success relates canonical return bytes and
whole effects/requests. UNREACHABLE permits ExHalt; dynamic strict decoding
has the precise D9 exemption. Proving this
contract belongs to Milestone 6.

### 1.4 Pipeline statement

D17 selected forward `unit_result_rel`, not equal failure observables; S4
now relaxes its Halt case to `dead_result_rel D`, equal outside a dead-byte set
`D`. S4 and S6 are stated for actual O1; S5 supplies memory/reachability. All
are proved.
Old pass APIs do not prove the executed driver, callee-first mixed contexts,
pruning or label mapping. F25/F26 remain concrete Milestone 3 inputs below.

### 1.5 Derivable hypotheses

The [L1–L13 table](compiler-proof-status-2026-10-09.md#clean-structural-producers-l1l13)
lists actual proved exports/owners, including initial-state, first-function,
layout, offset-zero and freshness producers. They are not public premises.
L1 extracts successful phases and `runtime_bc = assemble prog`;
L6/L7/L8 use one concrete `entry_venom_state`. L5 still consumes memory.

The 2026-09-29 identity-finalizer decision is implemented: `K SOME`, with
`finalize_codegen_identity`, not the unused/insufficient `finalizer_correct`
that only asserted target safety and never behavior preservation. Meaningful
single-frame deployment is covered by `e2e_deploy_correctness`.

### 1.6 Inventory cleanup

Historical inventory requested removal of dead O2/sparse-selector/kwargs/closed-
function helpers and superseded `gen_inst_simulation`, `gen_block_simulation`,
`asm_bytecode_sim`. Those are not current runtime APIs. D30 records why three
unused false local claims were retired rather than rewritten; output-state
freshness is now proved. Optional `compile_state_ok_*` work is not a stage
proof requirement. The [completed ledger](../lowering/e2eLegacy.md) maps all21
retired definitions and all14 final claim/helper entries, preserving original
proofs and exact Git identities, with no old/new bridge.

**Statement exit:** exact generic/top composition and named premise/admission
inventory exist. **Validation exit passed in [TASK060](compiler-proof-milestone-1-exit-2026-10-09.md)**;
this does not prove S1–S7.

## Milestone 2: First closed results

Goal: close the final, general theorem statements early, leaving only a few
named cheats for the cases not yet covered. There are two steps. 2.1 closes
the codegen stage. 2.2 closes the whole path from source to bytecode.

**The rule for both steps.**

- **No restrictions on the input.** Each theorem is the full statement from
  Milestone 1. It has no extra hypotheses limiting which programs it applies
  to. A result that holds only for a restricted class of programs may not
  extend to the full theorem. A general statement with a few missing cases
  does extend, because proving those cases later changes nothing else.
- **Only scoped cheats.** A *scoped cheat* is a separate, named lemma whose
  statement is exactly the proof obligation of one missing case, as it
  arises inside the general proof. The main proof uses the lemma and
  contains no `cheat` of its own. Proving the lemma later then closes that
  case without touching the main proof.
- **Proof sketches.** Each scoped cheat has an informal proof sketch in a
  comment above the lemma. The sketch says which invariants the proof needs
  and where they come from.
- **Checked by the dependency tool.** At the end of the step,
  `tools/cheat_audit.py deps` on the top theorem lists exactly the scoped
  cheats and nothing else.

### 2.1 Codegen and frame infrastructure

**Owner: Milestone 2.1, consuming S7 / codegenCorrectness.** This replaces the
old gas-bound/three-case recipe. Any future scoped sublemmas must match the
actual S7 statement; DELEGATECALL/CREATE/CREATE2 are inside `unit_shape_ok`, and
the theorem claims nothing about the delegated or created callee. No scoped lemma listed here is already exported
or proved. Concrete deferred inputs (PLAN T10.3 / 5.1–5.2 / 6.4):

| Handoff | Actual definitions / reusable input | Deferred contract and consumer |
|---|---|---|
| H21-frame | [frameOutcome](../venom/codegen/frame/frameOutcomeScript.sml) `frame_outcome`; L9 `frame_outcome_single_frame_run` | From wf/Collect nonempty Memory-output frame + actual `run_call` + absence of hard abort, derive single/nested `frame_outcome`. Cover parent pc/stack/logs/short splice, lower-frame FST preservation, saved snapshot CREATE caveat and nested failure rollback. L9 is only the **reverse single-frame bridge**; S7 owes this producer. |
| H21-hard | `initial_ctx_rel` supplies `wf_state` and `Collect`; Verifereum step/handle/run_call | Prove no OutsideDomain/Unimplemented/Impossible hard abort on reachable wf Collect runs, with wf preservation and required opcode/output boundary. Not a consequence of mere totality or “run returned SOME”. Feed H21-frame/S7. |
| H21-trace | [callTrace](../venom/codegen/frame/callTraceScript.sml) `observe`, `frame_obs_tr`, `request_of`, `outcome_of` | Decompose first-step entries/readings followed by continuation at our depth; for a pushed callee carry the **pending request/log count** through all descendants and append once on return. Preserve ordered complete sequence and suffix gas readings across same-frame runs; handle own faults and immediate balance/depth/precompile failures. Do not equate whole traces at a callee's depth or lose pending state. Feed oracle initialization/request equality in S7. |
| H21-static | EVM `step_call`/callee run; `adopt_outcome_static` is only an oracle-helper fact | Prove outgoing STATICCALL leaves live accounts/transient/logs unchanged even when **our caller frame is nonstatic**; include successful/failed callee and rollback. This establishes actual observed payload, not just abstract adoption. |
| H21-pure | `precompile_result`, `take_outcome_computed_valid`, `computed_precompile_state` in extCallOracle | For actual successful value-zero precompile1/2/6/7, prove bytes equal pure `precompile_result` and accounts/transient/logs unchanged. Separate invalid EC and successful empty ecrecover; a starved call is a failed oracle outcome, not part of this bridge. Abstract helper purity does not prove this EVM bridge. |
| H21-encoding | [asmWf](../venom/codegen/defs/asmWfScript.sml) `asm_encoding_wf`; `codegen_assembly`, target safety, assembled length <=24576 | Prove **all four actual encoding conjuncts**: opcode byte exists; recorded label offsets fit `symbol_size`; resolved `AsmPushOfst` offset+delta fits; push bytes <=32. Use actual generated output/no OFFSET and concrete offsets; label bound follows summed size <= assembled length <65536. Do not require `asm_wf` or positive sizes: data headers/empty items have size0. `asmEncodingRegression.encoding_wf_with_zero_size_data` / `zero_size_reverse_lookup` are focused existing checks, not this producer. |
| H21-lift | [evmStepSim](../venom/codegen/proofs/evmStepSimScript.sml) `asm_evm_step`, [asmBytecodeSim](../venom/codegen/proofs/asmBytecodeSimScript.sml) `asm_bytecode_sim_aux` | Lift current **one-frame/no-calls/non-GAS** proof interfaces to our frame with arbitrary parents, atomic observed CALL/STATICCALL and matched EVM gas readings. Use within-frame facts and H21-frame/trace/static/pure; conclude genuine resource alternatives or correspondence. Preserve old true non-GAS proofs, not an arbitrary exception loophole. |

**Known independently checked counterexample before repair:**
[asmOracleRegression](../venom/codegen/proofs/asmOracleRegressionScript.sml)
`gas_existing_relation_counterexample` / `gas_old_step_claim_false` show
`[AsmOp "GAS"]` with empty asm readings pushes0, while a related single-frame
EVM with gas100 pushes98 without exception. TASK041 checked the saved objects
before minimally restricting the old step/multistep claims. This is not a
failure/timeout inference. S7's future proof needs trace/readings alignment,
not reusing that old relation as a full GAS theorem.

Close non-INVOKE instruction emission cases of `gen_inst_ok_sim`,
`gen_inst_halt_sim`, `gen_inst_abort_sim` and the frame-aware function induction
(4.2); use H21-encoding/lift for EVM simulation. This tests S7's actual outcome
and resource contract. There is **no gas-sufficiency infrastructure requirement**
in the current theorem; quantitative bounds would be a separate future result.
None of this work is executed or newly certified by TASK058.

### 2.2 The whole path, closed except for scoped cases

Close the full supported-program contract from Milestone 1 without extra
restrictions beyond its existing boundary, following the same rule. The generic
composition is already proved; this step closes stage leaves, not a second
composition theorem. Codegen comes from 2.1. The
remaining scoped cheats in lowering and the pipeline should be for cases
of the same kind:

- internal function calls;
- supported calls to other contracts, creation included (CREATE/CREATE2 are
  inside `unit_shape_ok`; the created callee's correctness stays deferred);
- trace-aware GAS and assembly steps;
- ABI values of variable size, respecting the exact decoding exemption.

Deployment stays out of this step.

This step checks that the statements from Milestone 1 compose across all
stages. It exercises:

- the new lowering state relation;
- the per-function pass theorems;
- the label-map and pruning lemmas;
- the codegen result from 2.1.

## Milestone 3: Pipeline leg (O1)

**Owner: Milestone 3 / o1PipelineCorrect, S4 and S6.** Inputs are
`o1PassContract.dead_result_rel`, `ctx_sim`, `dead_wf`,
`raw_unit_memory_ok`, and `unitShapeDefs.o1_source_unit_ok` / `unit_shape_ok`.
S4 is forward simulation from **one initial state**: each terminating raw run
has a terminating output at possibly different fuel; success preserves
`observable_equiv` (including requests), abort preserves REVERT only. S6 must
produce output shape without changing compiler hooks.

### H3-findings: F25/F26 and executed-driver proof debt

These counterexamples are known from PLAN F25/F26 (2026-10-01 baseline);
this documentation does not newly execute or certify them. **First future
step: independently check the concrete witness against current definitions,
save the counterexample, then minimally repair the falsified contract while
preserving old proof text. Never attempt to prove the known-false closed
`dft_schedule_safe` premise.** An existing conditional pass theorem is not a
producer of that premise or proof of the driver.

| Input | Known witness / problem | Concrete obligation before S4/S6 can be proved |
|---|---|---|
| F25 schedule | `MSTORE %p %v; ASSERT %x; RETURN %p 32` schedules ASSERT first, falsifying closed `dft_schedule_safe`. | Check actual `dft_fn`/`dft_block`/`build_eda`, then new correctness argument under raw shape/memory. Do not cite `dft_pass_correct` as unconditional preservation. |
| F25 failure transport | ASSERT hoists before INVOKE or RETURNDATACOPY: INVALID vs REVERT, changed revert bytes; if callee STOPs, raw Halt vs output Abort. Two GAS instructions can swap. | D17 allows the first abort weakenings, not Halt->Abort. Raw shape excludes callee STOP/RETURN and ASSERT_UNREACHABLE. Prove call order/state-write barriers and permitted hoisting, not failure request/byte equality. |
| F26 entry / labels | Blocks `[B; A; X]`: B loads calldata/JNZ A X, A does GAS (or CALL)/JMP B, X STOP. SimplifyCFG can merge into entry B and start at A; Label in a terminator's value position counts as successor. | Independently check merge witness; carry `first_block_no_preds` and `label_positions_ok` from S2 through actual SimplifyCFG/label map. General well-formedness alone is insufficient. |
| F26 dispatched variants | MakeSSA/LowerDload/SUE/CFGNormalization APIs differ from dispatch; call exclusions, missing returndata/immutables and contradictory empty-label/layout premises. | Bridge or re-prove the **actual dispatched functions**, preserving successful observables. Old pass APIs alone prove neither S4 nor S6. |
| F26 whole driver | Pre-walk, pruning, label map, FmpLowering and callee-first mixed calling conventions lack semantic composition. | Per-function replacement with interprocedural INVOKE induction over mixed contexts, reachable-pruning and mapping arguments, then actual driver composition. |

Actual owners to inspect: [driver](../venom/defs/venomPipelineDriverScript.sml),
[dispatcher](../venom/defs/venomPassDispatcherScript.sml),
[schedule](../venom/defs/venomPassScheduleScript.sml),
[DFT definitions](../venom/passes/dft/defs/dftDefsScript.sml),
[conditional DFT correctness](../venom/passes/dft/proofs/dftCorrectnessScript.sml),
[SimplifyCFG](../venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml).
The executed sequence is SimplifyCFG/DretDesugar pre-walk, unreachable pruning,
then callee-first MakeSSA, LowerDload, ConcretizeMemLoc, FmpLowering, MakeSSA,
SimplifyCFG, SUE, DFT, CFGNormalization, followed by checks. PLAN's definition
comparison is proof input, **not executed-driver correctness evidence**.

The Milestone 3 plan was, roughly in dependency order (S4–S6 are proved now,
and no cheat this list names remains):

1. **Composition layer.** Prove `run_venom_pipeline_correct` from per-stage
   theorems. This requires:
   - per-function replacement preserving `run_context`, with an
     interprocedural induction hypothesis over INVOKE for callee-first mixed
     contexts;
   - semantic preservation by `apply_unit_label_map`;
   - lifting from `run_function` to `run_context`;
   - terminating-run forward lifting for `unit_result_rel`; reuse old
     `pass_correct` only where its actual variant/premises suffice;
   - chaining of the structural preconditions between passes.
2. **Bridge or re-prove on the dispatched variants:**
   - SingleUseExpansion (`sue_expand_function_supply`);
   - CFGNormalization (`cfg_norm_function_supply`; this also closes
     `cfg_norm_pass_correct`);
   - LowerDload (`lower_dload_function_supply`, without the vacuous
     `ld_no_mem_read`);
   - MakeSSA (`make_ssa_current_fn`, including PHI-containing input for its
     second run).
3. **Prove the open semantic cheat.** `simplify_cfg_fn_correct` is already
   about the dispatched function.
4. **Missing theorems:**
   - DretDesugar;
   - unreachable-function pruning ("execution reaches only FCG-reachable
     functions");
   - FmpLowering (large).
5. **DFT.** Replace the known-false global `dft_schedule_safe` requirement
   with a scoped argument for the executed scheduling algorithm and D17
   transport, after the independent counterexample check above.
6. **ConcretizeMemLoc:**
   - extend coverage to INVOKE, LOG, MCOPY and external calls;
   - prove non-overlap for the `compute_function_layout_*` allocator the
     pipeline uses;
   - cover the `fn_eom` metadata update.
7. **Structural cheats.** Keep the SimplifyCFG, SUE and LowerDload
   `ssa`/`wf` cheats only where a later pass theorem consumes them. Restate
   them on the dispatched variants.
8. **H3-shape / S6.** Prove entry function remains first/no params/no RET,
   reserved-label and operand/label restrictions, RETPC ASSIGN/PHI
   closure, and excluded opcodes. Track generated `formal_label_` names,
   FMP/RET forms in internal functions, function order and unchanged data
   segment. Output shape must not assert raw-only restrictions.

## Milestone 4: Codegen leg

1. **Local block cases in `genBlockSim`:**
   - `jmp`/`jnz`, using successor-transfer and PHI invariants (`djmp` is
     outside current `unit_shape_ok`, so its general simulator case is optional);
   - the four `assign` cases;
   - `log`, `assert_ok`, `assert_unreachable_ok`;
   - ASSERT abort, using `revert_postamble` label facts;
   - `some_name`: emit lemmas for every EVM-opcode instruction. This is the
     largest local item.
2. **H42-function / owner Milestone 4.2 (done):** the plan was to prove actual
   [venomToAsmProps.gen_fn_simulation](../venom/codegen/venomToAsmPropsScript.sml)
   by mutual fuel induction over INVOKE/RET, using `fnPlanDecomp` structural
   decomposition. It is proved now, and S7's `codegen_correct` uses it.

   | Actual input | Frame-aware invariant fact the proof needs |
   |---|---|
   | `fn_entry_state_rel`, `fn_has_retpc`, `unit_shape_ok` / `opaque_use_ok` | Fresh callee vars need not already be valued. Handle return-address variables and copies/PHIs under the actual entry relation. Use concrete `lo = SND (compute_label_offsets prog)`, `o2pc = build_offset_to_pc prog`, and actual return-label lookup. |
   | RET operand order / `IntRet` conclusion | At RET the callee stack is **exactly its RET operands above caller `rest`**, so JUMP pops the return destination and leaves `REVERSE ret.iret_values ++ rest` at `pc_ret`. Do not equate assembly return address with a source return-PC token. |
   | Assembly step stack behavior | Every emitted step leaves lower stack entries untouched below the operands it pops; allow arbitrary caller `rest`, not equality of whole model/real stack lengths. |
   | `closure_spill_byte`, `fn_return_state_rel` | Preserve caller spill bytes outside the **whole callee call-graph closure**, not just the immediate callee interval; preserve shared state/outcome suffix at internal return, while terminal observations omit leftover outcomes. |

   Define this running invariant before block induction. Existing
   `context_venom_asm_rel`/`venom_asm_rel` equal-length/value requirements cannot
   substitute for it. `reachability_closed`/`fn_entry_inv` supply actual
   instruction sites; the runtime proof supplies their witness, `raw_reachable vs0`.
   This was the planned proof
   design; `gen_fn_simulation` is proved now.
3. **asm→EVM / owner Milestone 4.3:** consume H21-frame/hard/trace/static/pure/
   encoding/lift. Initialize assembly with `gas_readings es` and actual trace
   outcomes; align CALL/STATICCALL requests and complete atomic callee outcomes,
   short writes and static preservation. Lift non-GAS/no-call/single-frame
   interfaces to the actual S7 frame contract. CREATE/CREATE2 are inside
   `unit_shape_ok`; source callee equivalence is Milestone7. The gas bound is a
   separate proved theorem, S7g `codegen_gas_sufficient`, not required by S7's
   resource disjunction.
4. **`codegen_correct`**, from the pieces above. Reuse proved
   `initial_state_bridge`, `block_insts_sim` and `terminal_asm_evm_final` only
   within their actual scopes; they do not already supply the new frame/trace
   or return-address invariant. S7 `codegen_correct` is proved now.

## Milestone 5: Cross-stage invariants

**Owner: Milestone 5 / vyperLoweringCorrect S2, loweringMemCorrect S3 and o1PipelineCorrect S5.**
These producers were ADMITTED statements at Milestone 1; all three are proved now.
The call tops reach S2's shape through `lower_vyper_runtime_unit_checked_source_shape`
(successful runtime lowering and `check_contract F`), whose
non-`raw_shape_free_program` cases are three proved shape lemmas; the deploy
tops use `deploy_unit_o1_shape_ok`, with three proved deploy cases.
Units with `DALLOCA` get S3's facts from
`lower_vyper_runtime_unit_memory_ok_from_no_wrap`, whose reachable no-wrap and
FMP-floor inputs the call tops produce from the memory-safe entry runs
(`selected_raw_memory`, through `lowered_unit_checked_dalloca_facts`): the
memory-safety check gives `dalloca_no_wrap` at every `DALLOCA` it reaches
(`mem_safe_point_dalloca_no_wrap`), so neither input is an S1 premise.
Actual memory API is
[unitTransformDefs](../venom/compiler/unitTransformDefsScript.sml), not the
older compat `lowering_memory_safe` interface, which was deleted: its proof
was a `cheat`, and it would not have established S3's raw-unit contract.

| Handoff | Input/contract at Milestone 1 | Proof planned at Milestone 1 |
|---|---|---|
| H5-S2 | Lowering success + `check_contract` + `raw_shape_free_program` -> `o1_source_unit_ok` | Inspect raw emission: only ALLOCA among allocation/FMP forms, no ASSERT_UNREACHABLE; RET only internal, STOP/RETURN only entry; fresh legal labels, read0 empty operands, first block no predecessor, restricted RETPC uses. This supplies S4/S6 raw shape, not a compile-success theorem. |
| H5-S3 | S1 boundary + `~source_exempt` -> `raw_unit_memory_ok` | Alloca-aware buffer/layout induction, checked `unit_alloca_budget`, memory accesses below frontier and frontier <2**256. Fresh empty memory alone proves nothing about later accesses. Exemption exclusion is essential: dynamic decoding may read unchecked wrapping offsets. |
| H5-S5 | Actual O1/output plan, S2/raw entry/S3 and matching initial FMP -> exists `Inv` with output memory + reachability | Transport frontier/allocation safety through dispatched passes, including early SimplifyCFG/DretDesugar/MakeSSA/LowerDload and ConcretizeMemLoc; prove generated spill-region non-overlap, safe reads/writes and successful-step spill preservation, including aggregate INVOKE returns. Deliver **one shared invariant witness** to L5/S7. |

`raw_unit_memory_ok ctx vs` means **exists `Inv`** with
`codegen_reachability_package Inv ctx vs` and, at every invariant instruction
site, `s.vs_alloca_next < dimword(:256)`, `inst_mem_ok_in_fn fn inst s`,
`dalloca_no_wrap inst s` and `w2n s.vs_initial_fmp <= w2n s.vs_fmp`.
`inst_mem_ok_in_fn` holds at a revert forwarding, and otherwise requires each
source read/write range to be **empty**, below the frontier
(`off + len <= s.vs_alloca_next`) or inside the dynamic region
`[vs_initial_fmp, vs_fmp)`. A zero-length range need not have a small offset. This is an actual-sites safety contract,
not byte-array length or “all memory initialized”.

In `raw_unit_memory_ok`, `dalloca_no_wrap` is a fact the memory-safety check
establishes, not a caller obligation; the caller's `DALLOCA` obligation is S1's
`dalloca_fmp_headroom`. The two definitions
([unitTransformDefs](../venom/compiler/unitTransformDefsScript.sml)):

```sml
dalloca_no_wrap inst s <=>
  inst.inst_opcode = DALLOCA ==>
  !sz_op sz.
    inst.inst_operands = [sz_op] /\ eval_operand sz_op s = SOME sz ==>
    w2n s.vs_fmp + ceil32 (w2n sz) < dimword (:256)

dalloca_fmp_headroom inst s <=>
  inst.inst_opcode = DALLOCA ==>
  w2n s.vs_fmp +
    MAX (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata))
        (2 ** 255 + 2 ** 64) < dimword (:256)
```

[contextCodegenRel](../venom/codegen/defs/contextCodegenRelScript.sml) defines
post-PHI `enters_block`/`fn_entry_inv`, ordinary incremented instruction
continuations, next-block entry and INVOKE callee-entry closure. Carry the
invariant at those states, not unincremented step results. S5 memory avoids
**all live context spill regions**; generated ordered layout/L2 does not prove
that accesses avoid them. No safety fact may be fabricated on the exempt path.

## Milestone 6: Lowering leg

**Owner: Milestone 6 / loweringRuntimeCorrect S1 and lowering proof owners.**
H6-compare below transcribes the construct/failure comparison inputs of PLAN
§6 into a durable handoff; conditions it attributes to the whitelist are the
Milestone 1 gate's (see the decision ledger). These are **definition comparisons and conditions**,
not proofs of S1 or a claim all inputs compile successfully. Definition owners:
[source interpreter](../semantics/vyperInterpreterScript.sml),
[value operations](../semantics/vyperValueOperationScript.sml),
[context/builtins](../semantics/vyperContextScript.sml),
[state/storage](../semantics/vyperStateScript.sml),
[ABI](../semantics/vyperABIScript.sml),
[expressions](../lowering/defs/exprLoweringScript.sml),
[statements](../lowering/defs/stmtLoweringScript.sml),
[module](../lowering/defs/moduleLoweringScript.sml),
[ABI encoder](../lowering/defs/abiEncoderScript.sml).
Proof consumers are `exprLoweringProps`, `stmtLoweringProps`, `abiEncoderProps`,
`moduleLoweringProps` and S1; their old admitted lemmas are not the oracle-aware
unit simulation by themselves.

### H6-compare: source/lowering comparison inputs

| Construct / source definition | Actual lowered path to compare | Required condition / concrete deferred proof input |
|---|---|---|
| Selector lookup / `lookup_function` | Linear dispatcher and generated selectors | Distinct names/selectors, no public getter; exact External/no-default/count/binding boundary. Prove dispatcher reaches named function, not an arbitrary table premise. |
| Calldata size, `bind_arguments` | CALLDATASIZE minimum, CALLDATALOAD/range checks | Canonical `calldata_encodes`; head sizes and every supported value shape, widths multiples of8. Establish alloca-aware arguments/vars relation. |
| Successful return / fallthrough | MSTORE/ABI RETURN, STOP/typed INVALID | `tx_return_bytes` handles raw return or `return_bytes` wrapping; typing excludes typed fallthrough. |
| Integer Add/Sub/Mul/Div/Mod / `evaluate_binop` | `compile_safe_add/sub/mul/div/mod` | Overflow, zero/div-min/-1 and range checks for signed/unsigned widths; prove matched runtime Abort, not merely equality on success. |
| Exp / `evaluate_binop` | `compile_safe_pow` | Literal base or nonnegative literal exponent, as the Milestone 1 whitelist required; the lowering refuses a negative literal exponent (`no_neg_exp_expr`/`no_neg_exp_fn`). |
| Decimal Add/Sub/Div/Mod/Mul | Safe decimal paths | Include corrected minimum decimal product D12i, zero/overflow and scaling bounds. |
| UnsafeAdd/Sub/Mul/Div | Word op and wrap/truncate | D12h corrected division-by-zero result0, MIN/-1 wrapping; preserve checked Div distinction. |
| And/Or/XOr, ShR/ShL, comparisons/Min/Max | Bit ops and `compile_compare` | Unsigned shift count; ShL restricted to256 bits; Eq/NotEq on word types, not hash-compared strings. |
| Not/Neg/Abs | Simple builtin/literal op paths | Not bool/uint256, Neg signed/decimal, Abs int256; excluded narrow/unsigned cases stay excluded. |
| AddMod/MulMod/PowMod256/AsWeiValue | Math/misc builtins | Same modular/scaled results and matched checks for admitted forms. |
| IfExp/literals, Empty/MaxValue/MinValue/Epsilon | Branch/literals/`typed_val_to_w256` | Word Empty only; correct typed byte literal encoding, fixed evaluation order. |
| `evaluate_convert` | `compile_type_convert` | Conversions admitted by `valid_conversion`; compare integer/decimal clamps and scaling, bound-before-truncate, bytes->address/decimal/narrow-zero-tail D12d–g, and bytestring length/shift paths. Empty-byte signed integer/decimal conversion has the exact D9 exemption. |
| Env, account, BlockHash/BlobHash | `compile_env_var`, BALANCE/EXTCODEHASH/size, builtin block paths | Full env/typed-account ties, corrected empty-account codehash; real nonzero block/window bounds D22. |
| ECRecover/SHA256/ECAdd/ECMul | Value-zero STATICCALL1/2/6/7 + ASSERT/buffer read | H21-pure bridge; success from the call's oracle outcome on both sides; invalid EC now source RuntimeError D12a, invalid recovery succeeds empty. Not pure: they consume an outcome. |
| Tuple/struct/aggregate args/tuple locals | Aggregate expression and buffer paths | Same evaluation order and value-memory layout; fixed-memory/name/internal-call restrictions matter. |
| `evaluate_abi_encode_bytes` | Builtin encode/ABI buffer path | Supported single-argument/flag form and corrected typed size rule D12j; same bytes incl dynamic multiblock encoding. |
| Static `evaluate_abi_decode` | `lower_abi_decode`/clamps | Prove exactly same acceptance/value for static targets; conversion errors **not exempt**. |
| Dynamic ABI tuple String/Bytes | Dynamic decoder offsets/end/padding | For source-accepted bytes same value. Source rejects nonzero padding that lowering accepts; raw Venom wraparound reads can survive where EVM starves. Test overlapping/out-of-order/head/trailing/short/overbound tails; exact D9 exemption, no blanket decoder correctness. |
| Storage scalar read/write | SLOAD/SSTORE/TLOAD/TSTORE | Full-word types only; actual initial/outcome storage validity. Narrow stored masking differs outside subset. |
| Fixed/dynamic arrays, Append/Pop | `compile_array_subscript`, dynamic append/pop | Signed/unsigned bounds, effect-free index/RHS; storage length invariant and corrected length-only Pop D12b. |
| Hashmap / `hashmap_slot` | `compile_mapping_subscript`/SHA3 | Admitted integer/bool/address key forms; no byte/nested/transient hashmap write claim; carry layout/hash separation. |
| Storage struct field | Field read/write paths | Write all admitted fields; read first field only. |
| AugAssign; AnnAssign/Name/Assign | Load/store/ALLOCA/local table | Effect-free RHS and global/arg/local/loop distinctness; buffer/PtrVar allocation relation rather than old fixed-pointer state assumptions. |
| If/Break/Continue/Return/Pass/Expr | JNZ/branch/return paths | Statement/list/control induction; no escaped control at external boundary. Internal returns require IntRet. |
| For range / `get_range_limits` | `compile_range_bound_checks`/loop path | Correct literal bounds/endpoints D13; endpoints once, runtime check iff not both literal. |
| For fixed memory array | Fixed-array iteration | Bound equals array length and safe element buffer access. |
| Internal Call / evaluator call path | INVOKE/callee lowering | Empty setup_callee fixed D14; effect-free arguments; no internal locals/nested internal calls/loop-body internal calls. Interprocedural unit-context proof, not single-function `run_blocks` shortcut. |
| External Call in SOME mode | CALL/STATICCALL + return decode/re-raise | Effect-free target/args/kwargs, exact interface/types/count, word/word-tuple return; kwargs and default evaluated in source order before the call; same requests/payload/decode. `NoneT` external return was not compared/admitted. Exhaustion is failed call, not stuck. |
| Send in SOME mode | CALL (gas operand or 0) + ASSERT | Empty-data request, effects adopted on success; source failure matched by Abort. NONE remains concrete transfer. |
| Log / concrete event encoder | Topic/data encode + LOG | Declared matching fields, supported indexed kinds; ordered concrete EVM events, not old symbolic log model. |
| Assert/Raise | REVERT/string payload or UNREACHABLE INVALID | Ordinary assertion requires Revert; UNREACHABLE allows ExHalt/failing frame. No revert bytes/reason equality. |

| Source failure family (H6-failures) | Boundary or proof obligation |
|---|---|
| Source lookup/code/module, argument count/binding | `source_deployment_rel` / `valid_vyper_call`; no-default/runtime context removes defaults/constants setup cases. |
| Nonpayable / entry transfer | Prove lowered CALLVALUE ASSERT match; transfer failures excluded by actual `value_transfer_ok`, not presumed success. |
| Storage decode / block hash / nonreentrant lock | Actual storage/outcome guards, `tx_env_ok`; nonreentrant excluded. |
| Arithmetic/conversion/bounds/runtime checks | Each H6-compare path must end in Abort on non-exempt RuntimeError, never Error/fuel exhaustion/OK/IntRet. |
| Oracle exhausted/failed/ill-typed successful accounts | Failed call -> ASSERT/REVERT; ill-typed accounts excluded by `call_outcomes_ok`, whose storage guard remains separate. |
| Exact `"abi_decode invalid"` | Dynamic target occurrence in **function bodies** gives D9 program-wide exemption; includes identical return-decode rejection. Static-only decoding, arbitrary ReturnReject and `"abi_decode conversion"` do not. Even exemption needs an actual EVM run; S3 safety is not claimed there. |

Comparison work of the 2026-10-01 plan (including finite8-bit arithmetic and
boundary samples) is not a kernel stage proof. Future owners must recheck
changed definitions/conditions, then prove these paths. The unchanged source
checkpoint receipts are historical evidence, not a fresh comparison rerun here.

1. **State relation.** `state_rel` relates locals through `local_ptrs_rel`
   (#625): a `PtrVar` pointer holds the base of a `vs_allocas` region holding
   `val_in_memory`. Still to add: full accounts and transient-storage
   equality and a `PtrVar` `__return_pc__`. Every body's locals are
   `PtrVar`s with their own `ALLOCA` (`declare_local`). Default arguments
   stay at `MemLoc` offsets that `state_rel` does not relate. The current gate
   admits checked defaults; S1's grouped-default, `msg.gas`-default and
   constant-name-default branches are proved.
2. **Expressions.** Restate the expression lemmas over `run_blocks` in
   `unit.cu_context`, INVOKE-aware, and then prove them: name, binop, neg and
   the others needed by the supported subset. `compile_expr_ci_mono`
   is proved.
3. **Statements.** Cover statements and statement lists, including the
   return/Halt/Revert/ExHalt outcomes, and internal returns through the
   `IntRet` lemma.
4. **ABI:**
   - `compile_abi_encode_to_buf_correct`, with multi-block dynamic cases;
   - static decode, restated to describe the decoded value;
   - external return: actual `tx_return_bytes` (including raw return or singleton wrapping).
5. **Module:**
   - linear dispatch reaches the entry for the calldata selector;
   - argument decoding establishes `local_ptrs_rel` in `state_rel`;
   - `lower_vyper_runtime_unit_correct`.
6. **Builtins.** Send/ExtCall use the complete
   outcome oracle; computed precompiles take their success from it and
   their data from pure results. The widened whitelist admits `raw_call` and
   the creation builtins (`raw_create`, `create_copy_of`,
   `create_from_blueprint`, `create_minimal_proxy_to`); their creation body
   cases and `raw_call` on `msg.data` are proved; what stays held is only the
   create-size claim at each entry, under the gas companions. Wire conversion
   proofs into the actual lowering rollup without inventing gas-number reads.
7. **H6-deploy / owner Milestone 6 item7:**
   `e2eDeployCorrectness.e2e_deploy_correctness` is proved, reaching no
   admitted lemma, using
   [e2eDeployDefs](../lowering/e2eDeployDefsScript.sml): `constructor_args_encode`,
   `deploy_typing_ok`, `deploy_storage_ok`, `deploy_state_rel`,
   `deploy_result_rel`. Constructors may make supported external calls,
   including the computed precompile builtins (sha256, ecrecover, ecadd and
   ecmul). The source run uses the creation frame's call outcomes.

   Inputs are canonical tuple ABI argument bytes (no selector), actual checked
   deployment/runtime artifacts (`deploy_typing_ok`, from which
   `deploy_typing_ok_constants_ready` gives **pre-constant deployment
   readiness**), an uninstalled source target, an empty target account in `es.originalAccounts`,
   and exactly one fresh nonstatic Code frame with
   `deploy_bc ++ args_bytes`, empty calldata/memory and live transfer (that the
   runtime has no 0xEF prefix is proved, `compile_vyper_runtime_not_ef`).
   The frame's call trace has fewer than 2⁶⁴ entries. Source reads of `self.code`
   use the creation frame's code, including in the assembly-optimizer case.
   Successful installation returns and deposits `runtime_bc ++ section`
   satisfying `immutables_section_rel`. The result relation compares accounts
   and transient storage at the run's storage horizon, ordered logs and call
   requests. The theorem includes a resource-exhaustion alternative. The result
   relation handles failure and source exemptions.
   Nested creation frames and general runtime immutables remain generalizations.

## Milestone 7: Full theorem

**Owner: Milestone 7 / environment and transaction corollaries.** Prove stage
and environment closure at their actual scope; do not call current top
composition fully verified. Concrete T10.3 inputs:

| Handoff | Actual definitions / partial input | Deferred contract |
|---|---|---|
| H7-fallback | `valid_vyper_call` excludes `__default__`; whitelist only allows argument-free fallback declaration | Extend call boundary/dispatcher reasoning for fallback invocation; no current producer or fallback correctness theorem is supplied by this roadmap. |
| H7-storage | `storage_ok`, `call_storage_ok`, `deploy_storage_ok`, `source_typing_ok`, `contract_storage_well_formed` | Deployment establishes and later transactions preserve exact installed-source/readiness, machine/tx typing and storage that decodes over the regions each call observes. The finite-trace storage guards are `call_storage_ok` (from a `valid_horizon` over the call's source storage trace by `valid_horizon_call_storage_ok`, or under closed-world premises by `closed_world_call_outcomes_ok`) and `deploy_storage_ok` (each gas filling's premise in `deploy_call_result_rel`, which `e2e_deploy_correctness` concludes for a creation run that is not resource-starved). Existing storage-preservation and call typing results are **conditional partial producers**. The finite-horizon ones (`call_external_storage_well_formed_on`, `load_contract_storage_well_formed_on`, and per construct `vyperFiniteStoragePreservation`) take a `valid_horizon` over the actual trace, or regions that decode before (`storage_well_formed_on`) with the trace's observations checked against them (`storage_observations_ok`), and conclude the regions decode after. The whole-contract ones (`vyperTypeEvalStoragePreservation`, `vyperTypeStoragePreservation`, `vyperCallOutcomeStorage`) take `contract_storage_well_formed` and, where they use them, `oracle_storage_ok` and, for the call and create adapters, `protected_storage_calls_preserve` or `protected_storage_creates_preserve`. Call machine preservation (`checked_call_external_preserves_machine_well_typed`) takes `checked_external_call_inputs_ready`. |
| H7-entry | `call_state_rel`, `source_deployment_rel`, `valid_vyper_call` | Construct a real top-level transaction entry with live transfer, wf/Collect, code/parser/length, fresh Memory frame, installed singleton source/layouts, exact ABI bindings and block ties. Prove **satisfiability of the combined environmental boundary**, not merely implication from it; no universal compile success or supported/satisfiable compiled-program witness exists here. D31 deliberately defers this. |
| H7-callees | `call_outcomes_ok` and source concrete `call_external NONE` / `load_contract NONE` | Prove the **source-executed-callee** producer: under explicit source typing/storage/protected-call assumptions, if the source itself ran every callee, all corresponding outcomes, including failed and static ones, satisfy the return-data length and account bounds of `call_outcomes_ok`, **and the caller's storage trace over them satisfies `call_storage_ok` (`deploy_storage_ok` for a constructor caller)**. No current such lemma exists; arbitrary EVM callee validity does not imply it. |
| H7-compose | Frame theorem / H21 trace and frame decomposition | Split actual nested execution into prefix, inner `run_call`, suffix with environment transports; apply separately to reentrant/multicontract entries. Compose transactions by persistent world-state induction, rebuilding a fresh **outcome trace oracle** at each top call and relating source gas observations to EVM readings. |

Read the [actual partial-producer premises](compiler-proof-status-2026-10-09.md#what-partial-producers-actually-establish)
before using typing/storage results. Runtime source readiness requires installed
sources/immutables, unlike pre-constant deployment readiness. Selected fresh,
nested, negative constructor and computed-SHA checks are interface evidence,
not H7-entry satisfiability or H7-callees proofs.

## Deferred

These do not block the first end-to-end theorem.

- **Optional pipelines.** O2/O3/Os certification and off-path optimization/
  shared-infrastructure admissions in the current dated audit. The old “45”
  tally belongs to its historical revision, not today's named128-site ledger.
- **Final assembly optimization.** The e2e theorem fixes the identity
  finalizer (1.5). A non-identity finalizer needs a semantic preservation
  theorem, which the dropped `finalizer_correct` never provided.
- **Frontend.** Parsing, JSON import and type checking remain trusted
  boundary inputs (see the specification).

## Parallel tracks

After Milestone 1, the work splits cleanly:

| Track | Scope | Shared interface |
|---|---|---|
| A: Lowering | Milestone 6 | `state_rel`, `lower_vyper_runtime_unit_correct` statement |
| B: Pipeline | Milestone 3 | per-pass relation vs `observable_equiv`; `run_venom_pipeline_correct` statement |
| C: Block codegen | Milestone 4.1 | actual `gen_inst_*_sim` interfaces; frame-aware integration still owed |
| D: Function codegen and asm→EVM | Milestone 4.2–4.4 | actual S7/frame contract, outcome trace, GAS readings, frame-aware function invariant |
| E: Invariants | Milestone 5 | memory and reachability invariant definitions |

Milestone 2.1 comes from track C and part of track D. Milestone 2.2
draws on every track.

## Evidence and validation boundary

This 2026-10-09 docs-only update reads/reuses accepted TASK056/057 evidence;
**no HOL, audit-tool, fixture, parity, generated or default build was run**.
No source/cheat/byte/fixture/cache changes. Durable source identities are
`e4cb0914` (integrated TASK056), original delivery `5ef7b04f`, and `e88dae75`
(accepted TASK057 docs base). The following absolute paths are **ephemeral
external receipts**, not repository links or promises of future persistence:

| Evidence identifier | Scope actually reused |
|---|---|
| `/tmp/m1-result-056.md`, `/tmp/m1-task056-evidence.json` | Exact top/generic schemas, named130->128 delta and source/proof preservation. JSON SHA256 `40886d2ec7ce0581c36f4ba671510e1a550991256ac80914107a88cde0de8ff1`. |
| `/tmp/m1-056-deps-final.txt`, `/tmp/m1-056-kernel-call.txt`, `/tmp/m1-056-kernel-composition.txt` | Saved top exactly S1–S7; generic and each L1–L13 zero leaves; top/deployment tagged separately. 104 call-gate objects:102 clean,2 classified admitted. These are prior saved-object checks, not new audits. |
| `/tmp/m1-integrated-056-roots1-guard.json`, `/tmp/m1-integrated-056-roots1.log`, `/tmp/m1-integrated-056-deps.log` | Current implementation `e4cb0914`, eight targeted roots/normal cache restore, top7/generic0. Logical closures378/30, no retired/deployment/gen_fn dependencies. Admitted build ancestors are not certified stages. |
| `/tmp/m1-result-057.md`, `/tmp/m1-task057-docgate-postcommit.json` | Accepted docs schema/source/export/link check with unchanged TASK056 source hashes. Static evidence only. This roadmap checks actual source names/owners and identifies these receipts; it does not re-save/audit kernel objects. |
| `/tmp/m1-result-041.md`, `/tmp/m1-result-045.md`, `/tmp/m1-result-055.md` | Identified prior local evidence for GAS counterexample-first/minimal repair, encoding-only zero-size reverse lookup and Call-free deployment boundary/negative nested-Call and allowed computed-SHA checks. These are not general generated-output wf or S7/function/deployment proofs. |
| Dated audit's TASK022/034/065 identifiers | Membership101, source checkpoint and exact-byte strict101 evidence retain original scopes/revisions. TASK065 parity is **historical only**, not final merged certification. |

The [dated status evidence table](compiler-proof-status-2026-10-09.md#evidence-provenance-and-remaining-checkpoint-debt)
is authoritative for receipt scopes/partial producers. Original source/gas/
codegen false-statement history remains in that audit and the earlier
[drafts/counterexamples](compiler-proof-drafts-and-counterexamples.md).
F25/F26 are reproduced in H3-findings from PLAN, not linked to a nonexistent
TASK059 report. The completed [twelve finding reports](findings/README.md)
cover F10–F16/F18/F21–F24 and remain local, not externally published.

**TASK060 complete:** the [final exit report](compiler-proof-milestone-1-exit-2026-10-09.md)
records final merged project/default/optional/module validation, 3820 selected
generated results, all101 memberships and strict compiler certificates,
202 independent unchanged byte lists, and final dependency/admission/
documentation checks. Earlier targeted gates retain their own scopes.
S1–S7/function/deployment proofs and Milestone7 producers/satisfiability remain
later milestones; final validation is not full compiler verification.
