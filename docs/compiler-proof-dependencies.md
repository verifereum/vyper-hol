# Compiler proof dependencies

Current Milestone 1 boundary: accepted primary `e4cb0914`, audited 2026-10-09.
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

```text
compile_vyper (K SOME) succeeds
  -> L1 actual rpolicy/raw unit/O1 out/assembly prog/plan cp
       runtime_bc = assemble prog (actual data segment/code-end header)

supported_program -> S2 raw source-unit shape -> S6 output shape
call_state_rel + shared entry_venom_state -> L6/L7/L8 initial relations
source typing/storage + valid ABI call + successful-outcome guards -> S1

non-exempt branch:
  S3 raw memory -> S4 forward O1 simulation
  S5 chooses Inv, output memory and reachability
  L2/L4/L5 + S5 memory -> structural codegen context obligations
  S7, using SAME Inv -> frame-aware EVM correspondence/resource alternatives

clean generic e2e_vyper_to_evm (explicit stage premises, zero admission leaves)
  -> vyper_call_correct (seven public premises; inherits exactly S1-S7)
exempt branch: actual total run + exact decoder exemption, not invented safety
```

The compiler is the actual `run_venom_pipeline ... o1_pipeline_spec`, not an
arbitrary mandatory-pass surrogate, a legacy pass pipeline, or an O2/O3 claim.
The finalizer is identity `K SOME`; no `finalizer_correct` assumption remains.
Memory/shape/policy/labels/initial state are **not extra public hypotheses**.

## All public hypotheses and producers

The exact [seven-premise schema](compiler-proof-status-2026-10-09.md#public-runtime-theorem)
is `e2eCorrectness.vyper_call_correct`.

| Hypothesis | Class | Current producer / absence |
|---|---|---|
| compiler returns `(deploy_bc,runtime_bc)` | boundary | Caller supplies success; L1 extracts raw phases and exact assembled runtime bytes. No universal success producer. |
| `supported_program tops` | computational boundary | 101 named `supportedFixtures*.*_supported_program` exports/plain EVAL at TASK022; exact manifest whitelist on `tops` alone. No universal membership, typing or semantic correctness producer. |
| `source_typing_ok tops am tx` | boundary + environmental | Checker artifact; partial `load_contract_establishes_checked_contract_runtime_ready`, `load_contract_establishes_machine_well_typed`, `checked_call_external_preserves_machine_well_typed`. No complete arbitrary-environment producer. |
| `source_storage_ok tops am tx` | environmental/layout/hash guard | Conditional `eval_stmt_preserves_contract_storage_well_formed` family and `take_adopt_call_outcome_storage_suffix`. No complete deployment/transaction producer; Milestone 7. |
| `call_state_rel tops runtime_bc am tx es` | environmental | No general producer or satisfiability theorem. L6/L8 **consume**, not produce, it; transaction corollary deferred to Milestone 7. |
| `valid_vyper_call tops tx calldata ret` | environmental ABI/function boundary | No general producer. Exact External lookup/no fallback/no defaults, count, binding and encoded calldata supplied by caller. |
| `call_outcomes_ok tops am tx (MAP SND (call_trace es))` | environmental successful-payload guard | **No current producer**, neither arbitrary EVM callee nor source-executed callee. Milestone 7. |

The [partial-producer detail](compiler-proof-status-2026-10-09.md#what-partial-producers-actually-establish)
is part of this inventory: runtime readiness requires installed exact sources
and ready immutables; deployment assumes initial typing, both checks/context/
constants setup; call machine preservation assumes `checked_external_call_inputs_ready`.
Storage preservation consumes runtime-storage consistency, protected-call,
call-evaluation and oracle-storage premises. These are not universal producers.

`call_outcomes_ok` quantifies **all successful records**, including static ones:
`accounts_runtime_well_typed co_accounts` and `contract_storage_well_formed` on
those accounts and `co_tStorage` in the actual source context. Account balance
`<2**256` and code length `<=24576` guards do not imply storage validity.
The evaluator checks account bounds on successful nonstatic adoption, not the
storage premise. Nothing here relaxes the existing type/storage oracle guards
or pretends an implemented universal storage validator exists.

## S1–S7: current admitted producers

Each row is **ADMITTED**, a final statement/memo with future proof owner.
The actual built top has precisely these seven leaves; generic composition
and each L1–L13 have zero. See [source owners and receipt](compiler-proof-status-2026-10-09.md#built-logical-admission-path).

| ID | Saved export | Consumes / produces | Future owner |
|---|---|---|---|
| S1 | `vyperLoweringCorrect.lower_vyper_runtime_unit_correct` | raw lowering, boundary/entry facts -> terminating source-unit execution | Milestone 6 |
| S2 | `vyperLoweringCorrect.lower_vyper_runtime_unit_source_unit_ok` | lowering + supported syntax -> `o1_source_unit_ok` | Milestone 5 |
| S3 | `vyperLoweringCorrect.lower_vyper_runtime_unit_memory_ok` | S1 boundary + non-exemption -> `raw_unit_memory_ok` | Milestone 5 |
| S4 | `o1PipelineCorrect.run_venom_pipeline_correct` | exact O1 success, raw shape/entry/memory -> forward transform correctness | Milestone 3 |
| S5 | `o1PipelineCorrect.o1_pipeline_memory_obligations` | O1, generated plan, raw shape/entry/memory -> existential `Inv`, output memory/reachability | Milestone 5 |
| S6 | `o1PipelineCorrect.run_venom_pipeline_output_shape` | exact O1 + raw source-unit shape -> output `unit_shape_ok` | Milestone 3 |
| S7 | `codegenCorrectness.codegen_correct` | assembly/plan, context/reachability, shape and initial relation -> run_call/frame/resource correspondence | Milestones 2.1 and 4 |

Pipeline result transport is success-observable preserving, forward and
terminating; failed-run return bytes/general abort kind/requests may differ.
Generated plan layout does not prove spill safety. Empty entry memory does not
prove raw memory validity. Opaque GAS use/labels are supplied by output shape,
not arbitrary label or caller-read gas oracles.

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
computed value-zero precompiles1/2/6/7 consume none. No callee source correctness
is presumed or proved.

Success relates canonical returns/accounts/transient/logs and full request
sequence. Requests are success-only; leftover outcomes are not final
observations. Non-exempt source failure requires target failure, without
revert-data/reason/general-kind equality. The sole exemption is exact
`RuntimeError "abi_decode invalid"` with a dynamic target occurring in a function
body (including a return rejection producing that same message); not arbitrary
`ReturnReject`, static-only decoding or conversion failure.

Resources are frame OutOfGas/StackOverflow or valid computed-precompile failure,
not an existential gas threshold. Entry `cc_gas=0`; Venom GAS stays unchanged
and opaque, CALL/STATICCALL oracle semantics ignore evaluated gas operands.
There is no static-entry/immutables/msg.gas/gas=/fallback guarantee or caller-read
gas oracle. Combined environmental satisfiability and transaction/callee
producers remain Milestone 7 work.

## Deployment, function simulation and retired contracts

`e2eCorrectness.e2e_deploy_correctness` is a meaningful **ADMITTED** single-frame
creation statement (Milestone 6 item7), not the old proved `T` placeholder.
It requires Call-free constructor bodies, canonical arguments, actual deployment
typing/storage/pre-constant readiness and an uninstalled source target; success
compares installed runtime bytes/accounts modulo target code/transient/logs.
`venomToAsmProps.gen_fn_simulation` is separately **ADMITTED**, Milestone 4.2,
with internal-return/frame relations. Both are **off the runtime call path**.

The [completed retirement ledger](../lowering/e2eLegacy.md) maps all21 obsolete
definitions/all14 claims to the new API, preserves exact original proof
provenance and records export absence. No live compatibility aliases remain.
Old counterexamples/proof history are retained in the
[historical audit](compiler-proof-status-2026-09-28.md), not relabeled current.
The four original clean structural public schemas remain preserved; their
names/receipts are in the dated audit, not replacement correctness certificates.

## Checked-power expression simulation

[`powerCheckedProps.checked_power_run`](../lowering/proofs/powerCheckedPropsScript.sml)
certifies execution of the emitted checked `Exp` fragment: nonnegative,
in-range powers return the encoded integer result; negative exponents and
overflow revert. Its premises tie literal options to the same well-typed
expression and sequential operand evaluations, with typed operand bounds and
fresh target variables. Arbitrary literal options alone are not a sound
interface.

[`exprSimBinopFrag.binop_frag_pow`](../lowering/exprSimBinopFragScript.sml)
lifts this execution certificate through `powerFragProps.binop_frag_power_run`.
[`exprSimOperators.compile_power_case_sim`](../lowering/exprSimOperatorsScript.sml)
then supplies the checked `Exp` induction step from simulation of smaller
expressions. `compile_bop_case_sim` and `compile_bop_ok` discharge that case;
[`exprSimMain`](../lowering/exprSimMainScript.sml)'s `compile_expr_sim_mutual`,
`compile_expr_sim` and `compile_expr_vv_sim` have no extra `power_sim_ok`
premise. The latter two retain their ordinary `expr_sim_pre` boundary.
`binop_frag_word_typed` excludes `Exp`, while `binop_frag_typed` handles it
using checked-expression/evaluation provenance, and `compile_bop_word_sim`
passes that provenance through `compile_bop_word_with_frag_sim`.

The checked-power execution and case certificates are audited for closed,
axiom-free, admission-free proofs. They do not remove unrelated ExpMod/shift
and #636 admissions or establish S1 above.
`powerDomainProps`, `vyperPowerDomainTest`, support-gate redundancy and folded
constant-power regressions are independent domain/acceptance checks, not
execution certificates. No source acceptance or runtime semantics is relaxed.

Signed negative endpoints such as `(-2)**255 : int256`, the odd-exponent guard
on the signed literal lower bound, and raw `IntT 1` post-EXP clamps remain
covered. Raw-width lowering guards do not introduce source legality rules:
`evaluate_type` rejects non-byte widths such as `IntT 1` and `IntT 9`.

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
