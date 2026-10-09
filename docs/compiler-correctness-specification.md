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
- ABI arguments, return data, and revert data;
- persistent and transient storage;
- memory and immutables;
- logs and externally visible account effects;
- success, return, halt, revert, and applicable error behavior.

Unsupported pinned-compiler features must be listed explicitly rather than hidden in failed compilation cases or catch-all theorem conclusions.

## Observational correctness

The source and EVM executions need not have identical internal states. Correctness should relate externally meaningful observations, expected to include:

- execution outcome;
- ABI-encoded return or revert data;
- persistent account state and balances;
- transient storage where visible within the transaction model;
- logs;
- created contracts and deployed runtime code;
- externally visible effects of calls.

Internal Venom variables, compiler temporary memory, spills, labels, stack layout, and program counters are simulation details rather than source observations.

The exact observation type/relation is a phase-2 deliverable. It should support composition and nested calls without requiring equality of irrelevant target internals.

## Calls and nested contexts

### Current Milestone 1 runtime contract (2026-10-09)

The broader intended scope elsewhere in this planning specification is **future
scope**, not today's certificate. The accepted primary source is `e4cb0914`.
The saved `e2eCorrectness.vyper_call_correct` is composed from **ADMITTED S1–S7**;
clean generic composition and structural producers do not prove those stages.
See the [dated audit](compiler-proof-status-2026-10-09.md#public-runtime-theorem)
and [dependency inventory](compiler-proof-dependencies.md) for actual owners,
partial/absent producers and built evidence. TASK060 final certification is not done.

The entire public theorem is:

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
  ?r es'. run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/ precompile_call_starved es \/
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
running the entire transaction. `call_state_rel` requires a fresh **nonstatic**
frame: wf_state/Collect mode, memory output, code exactly `runtime_bc`, its
`parse_code 0 FEMPTY` map, size <=24576, jumpDest NONE, PC0 and empty stack,
memory, logs and return data. Message caller/callee/value and transaction/block
fields agree with the source. Block number is nonzero and <2**255 and the hash
window obeys MIN256 <= length <=256. Entry value transfer succeeds and **live**
`es.rollback.accounts` are the post-transfer source accounts (not the saved
head rollback snapshot); transient storage agrees and source input logs are empty.

The exact singleton main source must already be installed at `tx.target`, with
no exports and declared layout slots. Runtime typing readiness likewise requires
installed sources and ready immutables; it is not readiness for an uninstalled
source target. No separate equality of target account code to runtime bytes is
required beyond the executing frame's code equation. `valid_vyper_call` selects
the exact External declaration, nonreentrant flag F, no defaults, no
`__default__`, exact argument count, successful bounded binding and encoded
calldata for the declared argument types; `ret` is the looked-up return type.

`frame_outcome` describes both single-frame and nested completion. In the nested
case our frame is popped, the parent receives the success flag/return data,
advances its PC and gets the actual short-write output-memory splice. Success
appends our logs; failure rolls back to the saved snapshot without appending
failed-frame logs. This defined boundary and selected witnesses are not a proof
of S7 or of environmental satisfiability.

### Outcome oracle, not a source gas oracle

`call_trace es` is the ordered request/outcome trace of **our frame**, not the
trace of every descendant instruction. Requests contain target/value/calldata,
static flag and live pre-call account/transient snapshots; outcomes contain
success, return bytes, post-call accounts/transient storage and logs. Source
`call_external (SOME (MAP SND (call_trace es))) am tx`, Venom and assembly take
these outcomes instead of executing callees. Successful nonstatic outcomes
adopt accounts (including storage/code), transient storage and logs; static and
failed outcomes do not adopt payloads. The source's NONE mode still executes
concrete calls and the two-argument initializer still starts with NONE/empty
requests. Arbitrary source SOME lists use this **same evaluator**, not a second
source semantics.

Computed value-zero precompiles1/2/6/7 are computed from pure input, consume no
outcome and record no request; they are filtered out of `call_trace`. Other
calls, including nonzero-value precompile calls, remain ordinary oracle calls.
Verifereum still executes callees and any reentrant calls; the oracle abstracts
that whole execution into an outcome. Re-applying a frame theorem to an inner
call requires its own premises. No current theorem connects all source-executed
callees to the EVM outcomes or proves a closed-world/reentrant composition.

`call_outcomes_ok` has **no current producer**. For every successful outcome
(including static ones) it requires the actual runtime account bounds (balances
<2**256, code length <=24576) and source contract-storage validity of the supplied
accounts/transient storage in the actual initial context. The source checks
account bounds on successful nonstatic adoption, **not storage validity**.
Type/storage preservation theorems consume guards; they do not weaken them or
manufacture a universal environmental producer. The detailed
[partial-producer audit](compiler-proof-status-2026-10-09.md#what-partial-producers-actually-establish)
records readiness/input/constants/protected-storage/oracle hypotheses.

The shared entry Venom state has **cc_gas=0**, concrete assembly labels and plan
FMP fields. Venom GAS is untouched, with opaque GAS results restricted to
CALL/STATICCALL gas operands; oracle call semantics evaluate then ignore those
values. Assembly uses frame-local EVM gas readings. There is **no caller-read
gas oracle**, source `msg.gas` guarantee or `gas=` keyword guarantee. The old
2026-09-29 gas-oracle account of this design is superseded by the outcome oracle.

### Observations, resources and limits

- Success requires a successful frame outcome, canonical `return_bytes`
  (empty NoneT, otherwise ABI with required singleton wrapping), equal live
  accounts/transient storage, ordered concrete logs and **the entire request
  sequence** equal to the observed trace requests. Requests are compared only
  on success; terminal leftover outcome lists are not related observations.
- Assertion/raise requires Reverted, except `"UNREACHABLE"` permits any failure.
  Non-exempt source Error requires a failed frame. Lowering requires a
  terminating Halt/Abort, never a stuck Error, OK, IntRet or fuel-zero escape;
  escaped Break/Continue/Return control has no corresponding result clause.
  There is **no revert-data/reason/general abort-kind equality**. The pipeline
  is a forward simulation with deliberately weaker failure observations.
- The sole exemption is exact `RuntimeError "abi_decode invalid"` when a function
  body contains a dynamic ABI decode target. It is not arbitrary ReturnReject,
  every decoder error, static-only decoding or `"abi_decode conversion"`.
  Callee-return rejection can be exempt only when it produces that same message
  in such a program. Exempt runs still have an actual EVM run but no result/effect
  correspondence obligation.
- Resource alternatives are genuine frame OutOfGas/StackOverflow, or a failed
  value-zero computed precompile whose pure input was valid. Invalid ecadd/ecmul
  input is not precompile starvation. There is no existential sufficient-gas
  loophole, gas bound or guarantee of success regardless of resources.
- Static entry, runtime immutables, msg.gas/gas=, fallback invocation and
  arbitrary unsupported programs are outside this runtime contract. Outgoing
  STATICCALL is not a static-entry guarantee. Environmental satisfiability,
  transaction entry/storage and callee-outcome producers remain Milestone 7
  obligations; selected boundary regressions do not discharge them.

Deployment is separate: the real `e2e_deploy_correctness` is **ADMITTED**,
Milestone6 item7, off this call path. It has Call-free constructor/canonical ABI,
pre-constant deployment typing/storage and fresh single-frame creation with an
uninstalled source target; it returns/installs runtime bytes and compares other
accounts and target modulo code, transient storage and logs. It is not the old
proved `==> T` placeholder. `gen_fn_simulation` is separately ADMITTED,
Milestone4.2, also off path. The
[completed retirement ledger](../lowering/e2eLegacy.md) retains original proof
history and maps all obsolete APIs to the clean new boundary; no compatibility
bridge is a current producer. Final project/generated/all101/strict bytecode
checks remain TASK060 debt; historical TASK065 parity evidence is not current
certification.

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
