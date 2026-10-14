# Compiler proof status — 2026-10-09 audit

**Milestone 1 statement/composition audit, not full compiler verification.**
The host `date -I` returned `2026-10-09`. Source baseline and accepted primary
HEAD: `e4cb09143b677747c4f857185e515b9c5999fe0c` (TASK056 integrated).
The initial TASK057 documentation audit reused identified saved-object receipts
without running HOL or tests. TASK060 subsequently passed the final combined
build, saved-kernel, coverage and independent-byte checks; see the
[2026-10-09 exit report](compiler-proof-milestone-1-exit-2026-10-09.md).

The [2026-09-28 audit](compiler-proof-status-2026-09-28.md) remains an unchanged
historical snapshot of `5c9b1738`, including its old statements and counterexamples.
See also [dependencies](compiler-proof-dependencies.md),
[Calls and nested contexts](compiler-correctness-specification.md#calls-and-nested-contexts),
and [earlier drafts/counterexamples](compiler-proof-drafts-and-counterexamples.md).
TASK058/059's [roadmap](compiler-proof-roadmap.md) and
[twelve local finding reports](findings/README.md) are complete.

## Public runtime theorem

The current saved export is `e2eCorrectness.vyper_call_correct`, in
[`lowering/e2eCorrectnessScript.sml`](../lowering/e2eCorrectnessScript.sml).
Its **entire** schema is:

```sml
!policy tops deploy_bc runtime_bc am tx ret es.
  compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\
  call_state_rel tops runtime_bc am tx es /\
  valid_vyper_call tops tx (FST (HD es.contexts)).msgParams.data ret /\
  call_outcomes_ok tops am tx (MAP SND (call_trace es))
  ==>
  ?r es'.
    run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/
     precompile_call_starved es \/
     call_result_rel tops ret am tx es r es')
```

`run_call` is Verifereum's frame run, not the retired local loop. The compilation
is the actual O1 `compile_vyper`, with identity finalizer `K SOME`. There are
exactly **seven** public premises: no extra gas sufficiency, Venom state,
selector table, shape, memory, invariant, context or policy-resolution premise.
Empty kernel hypotheses do not mean this theorem is unadmitted: its saved tag
inherits precisely S1–S7 below.

## All seven public premises

Definitions are in [`e2eDefs`](../lowering/e2eDefsScript.sml), except the compiler
and [`supportedProgram`](../lowering/supported/supportedProgramScript.sml).
“Producer” means a named result establishing the fact, not merely a definition
or a theorem that consumes it.

| Public premise | Classification | Named producer or explicit absence |
|---|---|---|
| `compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc)` | boundary: successful compiler run | Caller supplies success; **no universal success producer**. Proved L1 `e2eProducers.compile_vyper_runtime_phases` extracts the actual resolved policy, raw unit, O1 output, assembly, plan and `runtime_bc = assemble prog`, including data segment and code-end header. |
| `supported_program tops` | computational boundary on `tops` alone | The 101 exact manifest ASTs have named `*_supported_program` exports under `supportedFixtures*` (TASK022), each plain `EVAL_TAC`; e.g. `supportedFixturesMultiple.two_external_supported_program`. **No universal membership producer.** This is the exact syntax whitelist, not typing, layout safety, successful compilation or semantic correctness. |
| `source_typing_ok tops am tx` | boundary checker plus environmental readiness/machine/transaction bounds | `check_contract F` supplies an artifact; `vyperTypeContractSoundness.load_contract_establishes_checked_contract_runtime_ready`, `vyperTypeDeploymentMachine.load_contract_establishes_machine_well_typed` and `vyperTypeExternalCallMachine.checked_call_external_preserves_machine_well_typed` are **partial conditional producers**, detailed below. **No theorem produces the whole premise for arbitrary environments.** |
| `source_storage_ok tops am tx` | environmental storage validity and layout/hash separation guard | Conditional preservation: `vyperTypeEvalStoragePreservation.eval_stmt_preserves_contract_storage_well_formed` and its statements/expressions family; oracle adoption: `vyperCallOutcomeStorage.take_adopt_call_outcome_storage_suffix`. **No complete deployment/transaction producer** of this public premise. Milestone 7 remains responsible. |
| `call_state_rel tops runtime_bc am tx es` | environmental fresh-frame/live-state/source-installation boundary | **No general producer or satisfiability theorem.** L6/L8 consume it to produce initial simulation relations; they do not establish it. Milestone 7 top-level-transaction corollary is deferred. |
| `valid_vyper_call tops tx calldata ret` | environmental exact function/ABI input boundary | Caller supplies exact lookup, binding and calldata encoding; **no general producer**. Computable focused boundary checks are not a universal call-entry theorem. Fallback calls remain Milestone 7 work. |
| `call_outcomes_ok tops am tx (MAP SND (call_trace es))` | environmental successful-outcome account/storage guard | **No current producer.** In particular there is no theorem deriving it from arbitrary EVM callees or from source-executed callees. Milestone 7 source-callee execution result is future work; account/code bounds alone do not establish storage validity. |

### What partial producers actually establish

[`source_typing_ok`](../lowering/e2eDefsScript.sml) requires a successful runtime
checker, `checked_contract_runtime_ready`, `machine_well_typed`, and
`call_tx_well_typed`. Readiness means **the exact source modules are installed at
`tx.target` and the checked immutables are ready**, not that any arbitrary
machine or transaction is ready. In
[`vyperTypeContractSoundness`](../semantics/prop/vyperTypeContractSoundnessScript.sml),
`load_contract_establishes_checked_contract_runtime_ready` assumes successful
source deployment, a successful runtime check on the deployed layouts and
matching call/deployment targets. The
[machine deployment producer](../semantics/prop/vyperTypeDeploymentMachineScript.sml)
additionally assumes an initially typed machine, both deployment and runtime
checks, a main module, typed deployment context, and constants readiness.
The [call preservation producer](../semantics/prop/vyperTypeExternalCallMachineScript.sml)
assumes the check, runtime readiness, machine/transaction typing **and
`checked_external_call_inputs_ready`**. It preserves machine typing; it does
not manufacture all of `source_typing_ok` or readiness for arbitrary later calls.

[`source_storage_ok`](../lowering/e2eDefsScript.sml) uses the actual initial
source context and `initial_state am []`: `contract_storage_well_formed` and
`storage_layout_safe`. These are the real length/range, nonoverflow and
region-separation invariants, including hashmap separation assumptions, not
merely account bounds. The
[storage preservation family](../semantics/prop/vyperTypeEvalStoragePreservationScript.sml)
requires typing/runtime-storage consistency, well-typed functions,
`call_evaluation_safe`, `protected_storage_calls_preserve`, and
`oracle_storage_ok`; it preserves storage under those assumptions. Neither it
nor [oracle storage suffix/adoption facts](../semantics/prop/vyperCallOutcomeStorageScript.sml)
is an unconditional deployment or EVM-callee producer.

The source oracle's implemented account guard is unchanged:
[`take_call_outcome`](../semantics/vyperCallOutcomeScript.sml) checks successful
**nonstatic** payloads using
[`accounts_runtime_well_typed`](../semantics/vyperRuntimeAccountsScript.sml):
every account has balance `< 2 ** 256` and code length `<= 24576`. It does not
check contract storage or prove `call_outcomes_ok`. The public latter premise
requires those same account bounds **and actual contract storage validity** of
every successful payload, including static outcomes, in its initial source
context. Type/storage oracle guards in proof interfaces are assumptions or
conditional preservation facts, not an extra implemented storage validator;
no planned guard is silently weakened to “the oracle is trusted”.

## Entry, oracle and observations

`call_state_rel` supplies a fresh nonstatic head frame and arbitrary caller
frames below it: `wf_state`, `Collect` mode, `jumpDest = NONE`, memory output,
code exactly `runtime_bc`, `parse_code 0 FEMPTY runtime_bc`, code size `<=24576`,
PC zero and empty stack/memory/logs/return data. The source starts with empty
logs; entry value transfer must succeed. **Live** `es.rollback.accounts` equal
`accounts_after_transfer tx am.accounts`, not the saved head-frame rollback
snapshot; transient storage agrees. Caller/callee/value, origin, gas price,
chain id, timestamp, coinbase, block gas limit, fees, blob hashes, prevrandao
and block hashes agree. Block number is nonzero and `< 2 ** 255`, with
`MIN 256 block_number <= LENGTH block_hashes <= 256`.

The target **must already have the exact singleton main source installed**,
no exports, and declared layout slots, via `source_deployment_rel`. This is not
an uninstalled-target call theorem. Bytecode is tied to the frame's code;
there is no separate equation requiring the target account's code to equal
`runtime_bc`. Deployment has a different uninstalled-source boundary below.

`valid_vyper_call` uses the source's exact `External` function lookup, with
nonreentrant flag `F`, **no defaults**, exact declared argument count,
successful `bind_arguments (type_env tops)`, and `calldata_encodes` for the same
name/types/values. `__default__` is excluded. Return type `ret` is the looked-up
type. `return_bytes` is empty for `NoneT`, otherwise the ABI encoding with the
source's `needs_external_call_wrap` singleton-tuple rule, not always an
unwrapped value. These are bounds/binding and encoding obligations, not a
claim that all external inputs are valid.

[`call_trace`](../venom/codegen/frame/callTraceScript.sml) records our frame's
ordered `(request,outcome)` pairs. Requests contain target, value, calldata,
static flag and live pre-call accounts/transient storage; outcomes contain
success, return bytes, post-call accounts/transient storage and logs. The source
runs `call_external (SOME (MAP SND (call_trace es))) am tx`; Venom/assembly take
outcomes instead of executing callees. Successful nonstatic outcomes adopt
account/code/storage/transient/log payloads; static or failed outcomes do not.
`NONE` source mode still executes concrete calls; the two-argument
`initial_state am scs` still starts with NONE and empty requests.

Value-zero calls to computed precompiles 1/2/6/7 are computed by the shared
oracle helper and omitted from `call_trace`; they consume no oracle outcome
and record no request. Nonzero-value calls and other precompiles remain in the
ordinary trace. Callee/reentrant execution is absorbed into an outcome, not
certified as source-equivalent by this runtime theorem. Even arbitrary source
`SOME` lists use the same top-level source evaluator, not a second evaluator.

[`entry_venom_state`](../lowering/e2e/e2eEntryScript.sml) constructs the shared
fresh state from the live EVM environment: empty memories/variables/allocations,
concrete labels from `compute_label_offsets prog`, exact assembled code, three
FMP fields set to `n2w cp.cp_initial_fmp`, trace outcomes and empty requests.
It sets **`cc_gas = 0`**. Venom `GAS` is untouched; opaque GAS values may only
feed CALL/STATICCALL gas operands, whose values oracle calls ignore. Assembly
has frame-local EVM gas readings; **there is no caller-read gas oracle and no
`msg.gas` guarantee**.

### Result clauses and deliberate limits

- Source success requires successful `frame_outcome`, canonical ABI return
  bytes, exact live accounts/transient storage, ordered concrete event logs,
  and **the entire request sequence** equal to `MAP FST (call_trace es)`.
  Requests are compared **only on success**. Terminal leftover outcome lists
  are **not** observations required equal by this relation.
- Ordinary assertion/raise requires EVM failure with `Reverted`;
  `"UNREACHABLE"` permits any failing exception. There is **no correspondence
  of revert data, reason strings or general abort kind**. Pipeline abort
  transport preserves REVERT when required but may otherwise change abort kind,
  return data and failed-run requests; it is forward simulation, not full
  failure-observable equality.
- Non-exempt source `Error` requires a failed frame. Lowering specifically
  relates RuntimeError to `Abort`, never to `Error`, OK, IntRet or fuel-zero
  stuck execution. Escaped Break/Continue/Return control is unrelated.
- The **only exemption** is `RuntimeError "abi_decode invalid"` in a program
  whose function bodies contain a dynamic ABI decode target. It is a syntactic
  program-wide exemption, not “any decode error” or arbitrary `ReturnReject`.
  Because callee-return decoding uses the same exact error message, that
  rejection can also be exempt in such a program. Static-only decode and
  `"abi_decode conversion"` are not exempt. An exempt run has no result/effect
  correspondence obligation, but the theorem still supplies an actual EVM run.
- Resource escape is a genuine frame `OutOfGas` or `StackOverflow`, or an
  observed failed value-zero computed precompile with valid pure input
  (`precompile_call_starved`); invalid ecadd/ecmul input is not starvation.
  There is no existential “sufficient gas” loophole or guaranteed gas bound.
- No static **entry**, runtime immutables, `msg.gas`, `gas=` keyword, fallback
  invocation, arbitrary source program, closed-world callee or whole-transaction
  guarantee is supplied. Outgoing STATICCALL is distinct from static entry.
- Satisfiability of the combined environmental boundary and its transaction
  producers is **deferred**, not proved by selected fresh/nested regression
  witnesses. Neither this audit nor Milestone 1 claims a fully verified compiler.

## Built logical admission path

Current primary dependency receipt agrees with TASK056 saved-object audit:
`vyper_call_correct`: inherited cheat tag, **exactly seven direct admission
leaves**. Each entry below is **ADMITTED**, with a real stage statement and
proof-owner memo, not a proved stage.

| ID | Actual saved export | Contract / future proof owner |
|---|---|---|
| S1 | `vyperLoweringCorrect.lower_vyper_runtime_unit_correct` | terminating source-to-raw-unit simulation; Milestone 6 |
| S2 | `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok` | raw source-unit shape; Milestone 5 |
| S3 | `vyperLoweringCorrect.lower_vyper_runtime_unit_memory_ok` | raw memory validity on non-exempt executions; Milestone 5 |
| S4 | `o1PipelineCorrect.run_venom_pipeline_correct` | exact O1 forward semantic simulation; Milestone 3 |
| S5 | `o1PipelineCorrect.o1_pipeline_memory_obligations` | existential invariant, output memory and reachability package; Milestone 5 |
| S6 | `o1PipelineCorrect.run_venom_pipeline_output_shape` | output unit shape/opaque GAS/label facts; Milestone 3 |
| S7 | `codegenCorrectness.codegen_correct` | frame-aware generated-code simulation with resource disjunction; Milestones 2.1 and 4 |

Owners: [lowering](../lowering/vyperLoweringCorrectScript.sml),
[O1](../venom/compiler/o1PipelineCorrectScript.sml),
[codegen](../venom/codegen/codegenCorrectnessScript.sml).
The top obtains S1 even before checking source exemption. On the non-exempt
branch it consumes S3–S5/S7 and **the same `Inv` witness from S5**, with L5
supplying the remaining structural obligations. Empty entry memory alone
proves neither raw memory safety nor spill separation. S2/S6 supply shape.

`e2eCorrectness.e2e_vyper_to_evm` is the **clean generic composition theorem**:
no admission dependency, with lowering/transform/codegen contracts as explicit
premises. Importing admitted stage owners for definitions is not a logical
use of their admitted theorems. TASK056 records top/generic logical closures
of 378/30 nodes, with zero retired-API, deployment or function-simulation
logical dependencies.

## Clean structural producers L1–L13

Every export below was separately audited: empty `Thm.hyp`, no axioms,
no admission tags (ordinary DISK_THM bookkeeping ignored), **zero admission
leaves**. These produce structural/boundary consequences, not S1–S7 proofs.

| ID | Actual saved export | Produces |
|---|---|---|
| L1 | `e2eProducers.compile_vyper_runtime_phases` | actual compile/assembly/plan witnesses, exact runtime bytes |
| L2 | `contextPlanLayoutProps.generate_context_plan_layout_wf` | generated plan layout |
| L3 | `contextPlanLayoutProps.asm_pc_to_offset_zero` | assembly offset at PC 0 |
| L4 | `unitShapeDefs.entry_fn_first_lookup` | first entry function lookup |
| L5 | `e2eProducers.o1_pipeline_codegen_obligations` | structural codegen package, **assuming** supplied memory obligation |
| L6 | `e2eProducers.entry_venom_state_initial_venom_state_rel` | source/raw entry relation from call boundary |
| L7 | `e2eProducers.entry_venom_state_o1_initial_state_ok` | raw initial-state condition, no premises |
| L8 | `e2eProducers.entry_venom_state_initial_ctx_rel` | EVM/codegen initial relation from boundary and shape |
| L9 | `frameOutcome.frame_outcome_single_frame_run` | single-frame run bridge, **assuming** frame outcome |
| L10 | `emitHelperProps.fresh_label_output_inj` | label constructor injectivity |
| L11 | `emitHelperProps.fresh_label_produces_external` | freshness in the **output** compiler state |
| L12 | `e2eProducers.type_env_all_modules_single` | exact singleton main type environment |
| L13 | `contextPlanLayoutProps.ordered_spill_regions_SNOC` | ordered region extension |

Source owners: [e2eProducers](../lowering/e2e/e2eProducersScript.sml),
[contextPlanLayoutProps](../venom/codegen/proofs/contextPlanLayoutPropsScript.sml),
[unitShapeDefs](../venom/compiler/unitShapeDefsScript.sml),
[frameOutcome](../venom/codegen/frame/frameOutcomeScript.sml),
[emitHelperProps](../lowering/emitHelperPropsScript.sml).

## Off the runtime call path, retirement and proof history

- `venomToAsmProps.gen_fn_simulation` is separately **ADMITTED** for the
  real function-entry/internal-return relation; Milestone 4.2. It is not a
  logical leaf of the current call theorem.
- `e2eCorrectness.e2e_deploy_correctness` is separately **ADMITTED** (its own
  single admission leaf), Milestone 6 item 7. The old uncheated `==> T`
  placeholder is historical only. The current meaningful statement requires
  supported syntax, `constructor_call_free`, deployment typing/storage,
  canonical constructor arguments and fresh **single-frame** creation, no
  installed source at the target, code `deploy_bc ++ args_bytes`, memory empty,
  live entry transfer, and runtime not starting with `0xEF`. Deployment readiness
  is pre-constant setup, not runtime readiness for an uninstalled target.
  Success requires returned/installed runtime bytes, exact other accounts and
  target equality modulo code, transient storage and ordered logs; failures and
  resource/exemption cases are explicit. This is **stated, not proved**.
  See [deployment definitions](../lowering/e2eDeployDefsScript.sml).

Deprecated APIs are **fully retired**, not compatibility bridges. The
[completed ledger](../lowering/e2eLegacy.md) maps all 21 retired definitions
(and `_def` exports) and 14 claim/helper entries to the new API. It retains
original proof text in inactive archives and exact Git identities for the two
deleted owners. The old configured O1 wrapper, pair projection and legacy
codegen contracts are absent from the active saved API. Four original proved
public schemas remain clean: `e2e_venom_pipeline`,
`compile_vyper_runtime_bytecode`, and configured
`compile_vyper_with_success_phases` / `compile_vyper_with_deploy_runtime_compose`.
This does not claim every historical pass theorem is now applicable to O1.

**Actual source-site delta: 130 → 128, no additions.** TASK056 removed only
`e2eCorrectness.evm_correspondence_to_call_result` (local) and
`codegenCorrectness.codegen_correct_legacy`; all other site identities and
multiplicities were preserved. This is not a forced replay of the plan's
historical arithmetic or a theorem count. Earlier 136/123/127 counts belong to
their own revisions, not this baseline. Genuine old counterexamples remain
part of the history; repaired statements do not retrospectively prove old ones.

## Evidence provenance and remaining checkpoint debt

Durable identities: current sources at Git `e4cb0914`, TASK056 original delivery
`5ef7b04f`, producer/generic/deployment predecessors `f964c8e1`, `029a5361`,
`c5b53bbd`, `2fc79cd7`; TASK022 membership delivery `beb56b91`; TASK034 source
checkpoint `ace9f467`; historical TASK065 parity delivery `d9475b91` on
`ced53e70`. Git identities and linked source owners are durable; the absolute
report/log paths below are **ephemeral external receipts**, not repository
artifacts or a promise they will persist. Their checked contents are summarized
here; rebuild/audit tooling is [`tools/cheat_audit.py`](../tools/cheat_audit.py).

| Evidence read (not rerun here) | Scope and limits |
|---|---|
| `/tmp/m1-result-056.md`, `/tmp/m1-task056-evidence.json`, `/tmp/m1-056-deps-final.txt`, `/tmp/m1-056-kernel-call.txt`, `/tmp/m1-056-kernel-composition.txt` | Accepted LOCAL exact top/generic schema, Hyp/tag gates, L1–L13, four structural APIs, retirement and named 130→128 delta. 104 call-gate objects: 102 clean, top/deployment separately tagged. |
| `/tmp/m1-integrated-056-roots1-guard.json`, `/tmp/m1-integrated-056-roots1.log`, `/tmp/m1-integrated-056-deps.log` | Combined primary `e4cb0914`: eight targeted roots, successful normal cache restoration (4.670s), top exactly 7/generic 0. Stage/build ancestor admissions explicitly **not certified**. Not full project integration. |
| `/tmp/m1-result-022-final.md` | Historical LOCAL+ALL101 membership: 101 exact saved conclusions, Hyp0/no axioms/admissions, 14 group owners/plain EVAL proofs. Current manifest/fixture proof identities retained; final merged certification still TASK060. |
| `/tmp/m1-result-034-primary.md`, `/tmp/m1-evidence-034/primary/PRIMARY-VERIFIED.json` | Completed primary non-parity source checkpoint at `ace9f467`: 207 source theories/6 libraries, 254 generated theories, 127 cohorts/3820 exact results, 1456 closed source objects, union461 and coverage checks. Its legacy-owner classifications are historical, not today's saved API. No final-source suite replay inferred. |
| `/tmp/m1-result-065.md`, `/tmp/m1-task-065-evidence/` | **HISTORICAL ONLY** strict101 proof: 101 closed full compiler equalities, 202 exact deployment/runtime byte lists, 44,632 bytes, original plain EVAL endpoints. Its generic/deployment statuses predate this boundary and are not current. Not TASK060 certification. |

TASK056 receipt SHA256: evidence JSON
`40886d2ec7ce0581c36f4ba671510e1a550991256ac80914107a88cde0de8ff1`;
deps `e65c871445615d0cd8d2e2a8165ba467bdcbe422e882db1c8d871c91b785be0d`;
call kernel receipt `22e1aa0f585818aaf37cb0800cd5550482d29c4a1c7178079555e0ea5d6f4c98`.
The current primary source/saved-export names agree with these receipts; no
private cache is borrowed and no fresh kernel audit is claimed by this task.

**TASK060 complete:** the [final exit report](compiler-proof-milestone-1-exit-2026-10-09.md)
records 28 successful build operations and four kernel audits on combined
`0c622fda` (unchanged SML revision `e4cb0914`): full project/default/module
closure, 3820 selected results, all101 memberships and strict compiler
certificates, 202 unchanged independent byte lists, and final dependency/site/
documentation checks. Historical receipts above retain their original scopes;
they are not relabeled final evidence. No Milestone 1 checkpoint debt remains.
Proving S1–S7, off-path function/deployment simulation, and Milestone 7
environment/satisfiability/callee producers remains later milestone work.
