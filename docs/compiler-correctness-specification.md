# Compiler correctness specification

This document records the intended boundary and theorem family for the compiler correctness proof. It is a planning specification, not yet a claim that the corresponding theorems are proved.

## Authoritative compiler revision

The Python compiler revision is always the revision in [`../VYPER_PIN`](../VYPER_PIN). Compiler definitions, fixtures, language-test exports, and downstream generated inputs must use the same pin.

## Intended compiler boundary

The first correctness theorem begins after parsing and frontend elaboration. Its input is expected to consist of:

- a HOL representation of an elaborated Vyper module/AST;
- type and source/module information required by lowering;
- compiler metadata not formally recomputed from the AST;
- compiler settings, EVM version, and metadata policy;
- validity hypotheses connecting these inputs.

The parity audit must classify each metadata item as formally computed, related to external frontend output, or trusted. These assumptions should be packaged in a stable compiler-input validity predicate.

### Initially outside the theorem

Unless later brought into scope, the following are not verified by the first compiler theorem:

- parsing raw Vyper source;
- correctness of the Python JSON/AST exporter;
- complete Python semantic analysis and type checking;
- correctness of supplied metadata absent an explicit HOL relation.

These exclusions must remain visible in theorem statements or in a clearly referenced boundary predicate.

### Executions outside the current theorems

`vyper_call_correct` and `e2e_deploy_correctness` say nothing about an execution
their premises do not describe. Each limit below follows from a single conjunct
or check and is easy to miss:

- **A call frame runs the code installed at its own address.** `call_state_rel`
  (`lowering/e2eDefsScript.sml`) requires
  `(lookup_account tx.target es.rollback.accounts).code = ctxt.msgParams.code`,
  and its `frame_tx_rel` conjunct requires `ctxt.msgParams.callee = tx.target`.
  In a frame entered by DELEGATECALL or CALLCODE from a proxy, the callee is the
  proxy but the executing bytecode is the implementation's; in a call to an
  EIP-7702 delegated account, the executing bytecode is the delegate's, not the
  delegation designator installed at `tx.target`. Such a frame is outside
  `vyper_call_correct` whenever its executing bytecode differs from the code
  installed at `tx.target`, which is the usual proxy and delegation case; the
  conjunct compares only bytecode, so a frame whose executing bytecode equals
  that code (a self-DELEGATECALL, say) is not excluded by it. The conjunct makes the
  target an account with installed (nonempty) code, so a nested CREATE cannot
  land on it, bounds the length of the executing
  code (`call_state_rel_code_length`), and ties the account code the source reads
  for `self.codesize` and `self.codehash` to the code the frame executes.
- **Deployment is a single creation frame.** `deploy_state_rel`
  (`lowering/e2eDeployDefsScript.sml`) requires `es.contexts = [(ctxt, rb)]`. A
  creation frame running under a caller (CREATE or CREATE2 from a factory) is not
  an instance of `e2e_deploy_correctness`. The source models such a creation on
  the caller's side, through `eval_create` and the call-outcome oracle, and
  `vyper_call_correct` covers that caller: with no whitelist premise (next
  item), a calling body may create contracts or make a delegate `raw_call`, and
  the theorem takes the result of either from the call-outcome oracle.
- **No whitelist premise.** None of the four top theorems assumes
  `supported_program` or `supported_program_deploy`. Each derives them from
  the checker acceptance in `source_typing_ok` or `deploy_typing_ok` and the
  layouts that `call_state_rel` or `deploy_state_rel` fix, through
  `check_contract_supported_program` and
  `check_contract_supported_program_deploy`
  (`lowering/whitelist/whitelistCheckerGateScript.sml`).
- **Initcode is the deploy bytecode followed by the canonical constructor
  arguments.** `deploy_state_rel` requires
  `ctxt.msgParams.code = deploy_bc ++ args_bytes` and
  `constructor_args_encode tops tx args_bytes`. Initcode with trailing bytes, or
  with a non-canonical encoding of the constructor arguments, is outside the
  theorem; the source `load_contract` takes typed argument values, not raw
  initcode.

One conjunct reads like a limit but is not one: a deployment target that already
holds ether is covered. `deploy_state_rel` requires
`account_empty (lookup_account tx.target es.originalAccounts)`, which constrains
only the original-accounts snapshot. Verifereum resets the creation target's
entry in that snapshot to `empty_account_state` when a creation starts (both the
transaction-level creation and `proceed_create`). The live account comes from
`es.rollback.accounts = accounts_after_transfer tx am.accounts`, and nothing
constrains its balance to zero.

What the theorems compare on the executions they do cover is in
[Observational correctness](#observational-correctness) and
[Observations, resources and limits](#observations-resources-and-limits).

## Compiler stages

The first end-to-end result should compose:

1. Vyper-to-Venom lowering;
2. a named minimal mandatory Venom pipeline;
3. Venom-to-assembly generation;
4. assembly and symbol resolution to bytecode;
5. bytecode execution correspondence.

Optional O2/O3/Os pipelines are later interchangeable refinements, not prerequisites for the first theorem.

## Required functional scope

Subject to language features represented by the formal AST and pinned lowering definition, the intended scope includes:

- runtime and deployment compilation;
- internal function calls and returns;
- external calls and static calls;
- contract creation supported by lowering;
- nested EVM contexts;
- fallback and selector dispatch;
- ABI arguments and return data (for revert data, see [Revert data](#revert-data));
- persistent and transient storage;
- memory and immutables;
- logs and externally visible account effects;
- success, return, halt, revert, and applicable error behavior.

Unsupported pinned-compiler features must be listed explicitly rather than hidden in failed compilation cases or catch-all theorem conclusions.

## Observational correctness

The source and EVM executions need not have identical internal states. Correctness should relate externally meaningful observations, expected to include:

- execution outcome;
- ABI-encoded return data, and on failure that the frame failed (revert data is
  not compared; see [Revert data](#revert-data));
- persistent account state and balances;
- transient storage where visible within the transaction model;
- logs;
- created contracts and deployed runtime code;
- externally visible effects of calls.

Internal Venom variables, compiler temporary memory, spills, labels, stack layout, and program counters are simulation details rather than source observations.

The exact observation type/relation is a phase-2 deliverable. It should support composition and nested calls without requiring equality of irrelevant target internals.

### Revert data

The current theorems relate frame failure to source exceptions. For a source
`AssertException s`, `exception_outcome_rel`
(`lowering/e2eDefsScript.sml`) requires a failed frame outcome that is `Reverted`
and raised by the frame itself (`frame_raises es Reverted`), or any failure when
`s = "UNREACHABLE"`. The deploy relation `deploy_result_rel`
(`lowering/e2eDeployDefsScript.sml`) requires `Reverted` or, for
`"UNREACHABLE"`, any failure. A source
`Error (RevertData d)`, such as a bubbled `extcall` failure, requires a
`Reverted` frame outcome in both the call and deploy theorems. The call
relation also requires `frame_raises es Reverted`. For other source errors,
both relations accept any failed frame outcome. When
`unspecified_behaviour_exempt tops e` holds (see the exemption under
[Observations, resources and limits](#observations-resources-and-limits)),
any frame outcome is allowed. These relations quantify existentially over the
output bytes of `frame_outcome`. This leaves reason strings, custom error
payloads and bubbled revert data unspecified. The one exception is
calldata for which `calldata_dispatch tops tx.calldata = NONE`
(`semantics/vyperCalldataScript.sml`): a selector miss in a contract without
`__default__`, fewer than 4 bytes without `__default__`, or a selector hit whose
calldata is shorter than its static head or whose arguments fail to decode. There
`calldata_result_rel` requires `frame_raises es Reverted` and a `Reverted` frame
outcome with empty return data, unless the frame is resource-starved
(`frame_resource_starved`), the other disjunct of the conclusion. Deployment
failures carry these obligations only where its result relation applies:
`e2e_deploy_correctness` concludes `creation_resource_starved es r es' \/
deploy_call_result_rel ...`, and `deploy_call_result_rel` requires
`deploy_result_rel` only for gas fillings that satisfy `deploy_storage_ok`.
The guarantee that the output bytes equal `d` for `Error (RevertData d)` is
deferred.

## Calls and nested contexts

### Fixed storage regions

The public single-call theorem `vyper_call_correct` quantifies over a fixed
set of storage regions and lock slots `H`. Its storage premises are
`storage_ok H am tx`, which requires the initial source state to decode on
those regions, and `call_within H tops am tx es`, which checks the dispatched
source storage trace for every gas filling. The trace check includes the
storage backends the source adopts from external call outcomes.

```sml
  !fin policy tops deploy_bc runtime_bc am tx es H.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    storage_ok H am tx /\
    call_within H tops am tx es
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       calldata_result_rel H tops am tx es r es')
```

Outside the resource-starvation case, unmatched calldata raises an empty
revert. For dispatched calldata, `call_result_rel H` requires result
agreement at the run's own storage horizon and `storage_ok H am' tx` for the
source machine returned by the call, for each filling covered by
`gas_readings_rel`. The guarded theorem `vyper_call_correct_guarded` supplies
the underlying per-filling result.

### Milestone 1 runtime contract (2026-10-09)

The following subsections document the Milestone 1 boundary at `e4cb0914`.
At that revision, `e2eCorrectness.vyper_call_correct` composed **ADMITTED S1–S7**;
clean generic composition and structural producers do not prove those stages.
See the [dated audit](compiler-proof-status-2026-10-09.md#public-runtime-theorem)
and [dependency inventory](compiler-proof-dependencies.md) for actual owners,
partial/absent producers and built evidence. [TASK060 final validation](compiler-proof-milestone-1-exit-2026-10-09.md)
is complete, without proving the admitted stages.

The current statement is under [Fixed storage regions](#fixed-storage-regions);
its unmatched-calldata arm is described under [Revert data](#revert-data).

The entire public theorem was then:

```sml
!policy tops deploy_bc runtime_bc am tx ret es.
  compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\
  call_state_rel tops runtime_bc am tx es /\
  valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
  call_outcomes_ok am tx (MAP SND (call_trace es))
  ==>
  ?r es'. run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/
     call_result_rel tops ret am tx es r es')
```

This is the actual O1 compiler with identity finalizer `K SOME`, not an
arbitrary minimal/custom pipeline. Exactly seven public premises remain;
L1 produces raw/O1/assembly/plan witnesses and exact runtime bytes from compile
success, and L6–L8 construct initial relations from the supplied boundary.
The whitelist `supported_program` is computational syntax on `tops` alone,
with 101 fixture membership proofs; it is not typing or semantic correctness.

### One fresh frame, including nested callers

A call frame is the head EVM context. `run_call` is Verifereum's execution until
that frame ends; parent frames below it are arbitrary. It is not a claim about
running the entire transaction. `call_state_rel` requires a fresh frame, static or
not (`ctxt.msgParams.static = tx.is_static`): wf_state/Collect mode, memory output, code `runtime_bc ++ section` with
`immutables_section_rel tops (account_immutables am tx.target) section`, its
`parse_code 0 FEMPTY` map, size <=24576, jumpDest NONE, PC0 and empty stack,
memory, logs and return data. Message caller/callee/value and transaction/block
fields agree with the source. Block number is nonzero and <2**255 and the hash
window obeys MIN256 <= length <=256. Entry value transfer succeeds and **live**
`es.rollback.accounts` are the post-transfer source accounts (not the saved
head rollback snapshot); transient storage agrees, source input logs and pending
deletions are empty, and `es.rollback.toDelete` equals the pending deletions.

The exact singleton main source must already be installed at `tx.target`, with
no exports and declared layout slots. Runtime typing readiness likewise requires
installed sources and ready immutables; it is not readiness for an uninstalled
source target. The live target account's code must equal the executing frame's
code. In the 2026-10-09 statement, `valid_vyper_call` selected
the exact External declaration, nonreentrant flag F, no defaults, no
`__default__`, exact argument count, successful bounded binding and encoded
calldata for the declared argument types, and `ret` was the looked-up return type;
the current theorem has no such premise and cases on `calldata_dispatch` instead.

`frame_outcome` describes both single-frame and nested completion. In the nested
case our frame is popped, the parent receives the success flag/return data,
advances its PC and gets the actual short-write output-memory splice. Success
appends our logs; failure rolls back to the saved snapshot without appending
failed-frame logs. This defined boundary and selected witnesses are not a proof
of S7 or of environmental satisfiability.

### Outcome oracle and source gas observations

`call_trace es` is the ordered request/outcome trace of **our frame**, not the
trace of every descendant instruction. Requests contain target/value/calldata,
static flag and live pre-call account/transient snapshots; outcomes contain
success, return bytes, post-call accounts/transient storage and logs. Source
`call_external (SOME (MAP SND (call_trace es))) gobs am tx`, Venom and assembly take
these outcomes instead of executing callees. Successful nonstatic outcomes
adopt accounts (including storage/code), transient storage and logs; static and
failed outcomes do not adopt payloads. The source's NONE mode still executes
concrete calls. Arbitrary source SOME lists use this **same evaluator**, not a second
source semantics.

Computed value-zero precompiles 1/2/6/7 take their success from the next
outcome (the EVM can fail them for lack of gas) and, on success, their return
data from pure input. They record a request like any other call, so
`call_requests es = MAP FST (call_trace es)`: when the run succeeds or halts,
the k-th source request agrees with the k-th trace entry's under `request_agree`
(the builtin's request has no gas, so
the STATICCALL's forwarded gas is unconstrained). The source's sha256/ecrecover/ecadd/ecmul builtins take
that outcome too, through a static value-zero request to 2/1/6/7 carrying the
input bytes the lowering passes (`precompile_input`). One path still differs:
an ecadd/ecmul argument that is not a valid curve point makes the source raise
before any request, while the compiled STATICCALL records one before its
ASSERT aborts; `call_result_rel` compares effects only on success or halt, so
this mismatch is outside what the theorem relates. Constructors take outcomes
from their creation frame's trace through
`load_contract (SOME (MAP SND (call_trace es))) ...` in `deploy_call_result_rel`.
Other calls, including nonzero-value precompile calls, remain ordinary oracle calls.
Verifereum still executes callees and any reentrant calls; the oracle abstracts
that whole execution into an outcome. Re-applying a frame theorem to an inner
call requires its own premises. No current theorem connects all source-executed
callees to the EVM outcomes or proves a closed-world/reentrant composition.

`call_outcomes_ok` requires return-data length `< 2**256` and
`accounts_runtime_well_typed` for every outcome, including failed and static
ones. `call_state_rel_call_outcomes_ok` and `deploy_state_rel_call_outcomes_ok`
derive the guard for `MAP SND (call_trace es)` from the call and deploy state
relations, respectively. The finite trace guards `call_storage_ok` for runtime
calls and `deploy_storage_ok` for constructors check the storage regions and
backends observed by the source execution for the chosen gas readings.

The shared entry Venom state has **cc_gas=0**, concrete assembly labels and plan
FMP fields. Venom GAS consumes the frame-local `gas_readings es`, returning zero
when exhausted; assembly also uses frame-local EVM gas readings. There is **no caller-read
gas-reading correspondence** and no source `msg.gas` guarantee. For `gas=`, the
theorem relates only the operand: where requests are compared (success or halt),
`request_agree` requires `r1.cr_gas = SOME g ==> r2.cr_gas = SOME g` of every
compared request. Among the call forms the theorem covers (`extcall`,
`staticcall`, `send` and `raw_call`, delegate form included), a call with an
explicit source `gas=` value therefore forwards exactly that gas operand on its
CALL, STATICCALL or DELEGATECALL, and a `send` without `gas=` records 0, so its
operand must be 0. The operand of any other call without `gas=` is unconstrained,
creations and the precompile builtins record none, and the gas the callee
actually receives is not related.
The result relation ties source gas observations to the frame's EVM gas readings only through `gas_readings_rel (gas_readings es)`: it fixes some slots of the source's gas observations so that the fixed (`SOME`) slots together with the unused readings are a permutation of `gas_readings es`, and the result must hold for every value in an unfixed (`NONE`) slot and every appended tail, which the EVM readings do not constrain. The old
2026-09-29 gas-oracle account of this design is superseded by the outcome oracle.

### Observations, resources and limits

- Success requires a successful frame outcome, `tx_return_bytes` (raw return
  bytes for raw-return functions, otherwise `return_bytes`), account agreement
  after EVM pending deletions and transient-storage agreement modulo dead target
  storage, ordered concrete logs and
  `LIST_REL (request_agree H tx.target) rqs (call_requests es)`, where `H` is the
  run's own storage horizon in `call_result_rel_at`, not the theorem's fixed
  `H`. A source halt (`HaltException`) requires a successful
  frame outcome with empty output, the source's ordered logs and the same account,
  transient-storage and request agreement (`effects_agree`). Requests and these effects are compared
  only on success or halt; `exception_outcome_rel` compares none of them on
  failure. Terminal leftover outcome lists are not related observations.
- Assertion/raise requires Reverted, except `"UNREACHABLE"` permits any failure.
  A source `Error (RevertData d)` requires `Reverted` in both the call and deploy
  theorems. Other non-exempt source errors require a failed frame of any kind.
  The failure payload is unspecified in these cases (see
  [Revert data](#revert-data)). Lowering requires a
  terminating Halt/Abort, never a stuck Error, OK, IntRet or fuel-zero escape;
  escaped Break/Continue/Return control has no corresponding result clause.
  The pipeline is a forward simulation with deliberately weaker failure
  observations.
- The sole exemption is exact `RuntimeError "abi_decode invalid"` when a function
  body contains a dynamic ABI decode target. It is not arbitrary ReturnReject,
  every decoder error, static-only decoding or `"abi_decode conversion"`.
  Callee-return rejection can be exempt only when it produces that same message
  in such a program. Exempt runs still have an actual EVM run but no result/effect
  correspondence obligation.
- The resource alternative is genuine frame OutOfGas/StackOverflow. A
  value-zero computed precompile that the EVM fails for lack of gas is not an
  alternative: its failure is the call's oracle outcome, which the source and
  Venom both take. The call theorem gives no gas bound or guarantee of
  success regardless of resources; the companion `vyper_call_gas_sufficient`
  does: with enough gas the run exists. On unmatched calldata that run runs
  out of gas only if it reaches a `RETURNDATACOPY` instruction
  (`frame_inst_at`). When `calldata_dispatch` selects a source call, the same
  holds provided the raised-gas run's call trace has `call_storage_ok` for
  every gas filling of its outcomes, no exempt source observation
  (`~gas_source_exempt`) and fewer than 2⁶⁴ entries. The identity
  case composes proved lowering, O1 fuel/memory and codegen gas bounds. The
  assembly-optimizer case is proved from the same stages. The general
  companion reaches exactly one admitted lemma,
  `call_entry_reachable_create_size_ok`, marked `GATE_ADMISSION`: from the
  call entry, every reachable creation instruction meets the init-code size
  check. The correctness tops reach no admitted lemma. The deploy companion
  `e2e_deploy_gas_sufficient` similarly composes proved stage bounds and
  reaches exactly one admitted lemma, `deploy_entry_reachable_create_size_ok`,
  the same claim at the deploy entry; with enough added gas, and under
  its source-exemption, storage and trace-length (fewer than 2⁶⁴ entries)
  conditions on that raised-gas run, OutOfGas implies that the code to deposit
  is oversized or that the frame reached a `RETURNDATACOPY` instruction.
  Both deploy finalizer cases include these alternatives.
- msg.gas beyond `gas_readings_rel`, `gas=` beyond its forwarded operand and
  arbitrary unsupported programs are outside this runtime contract. Static entry
  (`ctxt.msgParams.static = tx.is_static`), runtime immutables (`installed_code_rel`
  over `account_immutables am tx.target`) and a `__default__` reached by
  `calldata_dispatch` are covered. Environmental satisfiability,
  transaction entry/storage and callee-outcome producers remain Milestone 7
  obligations; selected boundary regressions do not discharge them.

`e2e_deploy_correctness` covers fresh single-frame creation with
canonical constructor arguments, deployment typing, an uninstalled source
target and an empty target account in `es.originalAccounts`. It requires fewer
than 2⁶⁴ entries in the creation frame's call trace. Source reads of `self.code`
use the creation frame's code, including in the assembly-optimizer case. With
the finite storage guard, the result relation uses the constructor's call outcomes and
compares accounts and transient storage at the run's storage horizon,
along with logs and call requests. Successful installation returns and deposits
`runtime_bc ++ section` satisfying `immutables_section_rel`.
`venomToAsmProps.gen_fn_simulation` (Milestone 4.2) is proved; S7's
`codegen_correct` uses it through `codegenEntrySim`. The
[completed retirement ledger](../lowering/e2eLegacy.md) retains original proof
history and maps all obsolete APIs to the clean new boundary; no compatibility
bridge is a current producer. Final project/generated/all101/strict bytecode
checks passed in [TASK060](compiler-proof-milestone-1-exit-2026-10-09.md);
historical TASK065 parity retains its original scope, not the final certificate.

## Pipeline configurations

### Initial configuration

Define a dedicated minimal pipeline containing only transformations required to make lowering output acceptable to codegen. Its theorem must provide both semantic preservation and the codegen-readiness invariants consumed downstream.

### Optional configurations

O2, O3, Os, and custom pipelines should later be proved as alternative certified implementations between the same lowering and codegen interfaces.

## Memory safety and codegen readiness

Memory safety is included to the extent required by end-to-end correctness. The proof should first identify exact downstream requirements, such as:

- agreement between lowered ALLOCA instructions and runtime allocations;
- correct allocation-base values in variables;
- bounds for derived pointers;
- separation of compiler spill memory from program allocations;
- validity of ABI and temporary buffers.

Lowering must establish these conditions and mandatory passes must preserve them. A broad standalone `lowering_memory_safe` theorem is optional unless it is the best interface for discharging these obligations.

## Environmental assumptions

The final statements will need explicit assumptions concerning at least:

- valid elaborated compiler input and metadata;
- selected EVM version/fork;
- sufficient fuel or the appropriate terminating execution relation;
- gas modeling differences between source and EVM semantics;
- behavior/specifications of external contracts not compiled in the same closed world;
- cryptographic and host operations inherited from Verifereum;
- absence or treatment of target resource exhaustion.

Phase 2 must distinguish genuine environment assumptions from compiler invariants that earlier stages are responsible for proving.

The executions the current theorems do not cover at all (proxy and delegated frames whose executing bytecode differs from the target's code, nested creation frames, non-canonical initcode) are listed in [Executions outside the current theorems](#executions-outside-the-current-theorems).

## Planned theorem family

Prefer a family of composable results over one monolithic theorem.

### Stage theorems

- lowering correctness;
- minimal-pipeline semantic and invariant preservation;
- Venom-to-assembly simulation;
- assembly-to-EVM simulation;
- codegen correctness.

### End-to-end theorems

- runtime external-call correctness;
- deployment correctness;
- correctness with the minimal mandatory pipeline;
- O2/O3/Os correctness corollaries;
- nested/multi-contract composition where assumptions permit.

## Specification completion criteria

This specification is stable enough for major proof work when:

- every compiler input is classified at the formal boundary;
- source and target observations are defined;
- the minimal pipeline is identified;
- calls/nested-context semantics are selected;
- environmental assumptions are explicit;
- stage theorem statements compose without unproved hidden side conditions;
- known counterexamples no longer apply to the proposed statements.
