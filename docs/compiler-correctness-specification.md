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

A compiled contract can call other contracts, and those calls can call back into it. The theorem must cover such programs. A theorem restricted to programs without calls, or to a single EVM execution context (`LENGTH es.contexts = 1`), is not the final codegen theorem.

A *call frame* is one EVM execution context: the code being run, its stack, memory and program counter. A contract call pushes a new frame onto Verifereum's context list (`es.contexts`), and returning pops it.

**How the proof treats calls** (decided 2026-09-29, following the discussion on [#98](https://github.com/verifereum/vyper-hol/issues/98); roadmap Milestone 1.1 has the details):

- **One frame.** The theorem covers one frame running the compiled contract. Any frames below it, belonging to the callers, are arbitrary. It is stated with Verifereum's `run_call`, which runs the EVM until the current frame returns and then stops. So the theorem describes one call into the contract, whether it is the top-level transaction or a call from another contract.
- **A call is a single step.** When the contract calls another contract, the source semantics and the compiled code both leave the entire callee execution to Verifereum, including any further calls it makes, even calls back into our contract. The assembly-to-EVM proof treats a call instruction, together with everything the callee does, as one step of our frame.
- **Calls back into the contract.** For those, the theorem is applied again, separately, at the point where the inner call starts. The theorem therefore never needs to assume its own correctness for inner calls.
- **Gas.** Gas amounts the source program reads, like `msg.gas` or the gas given to a call, come from a list of values supplied from outside the source semantics. The theorem requires these values to equal the ones the compiled code actually sees during its EVM execution.

The rejected alternative was to give the assembly semantics its own model of the frame stack, so that the proof would follow execution into and out of every callee. That would need a source semantics that also runs callee contracts, and a correctness argument that holds for calls back into the contract being proved.

The design must still cover return data, reverts, undoing or keeping state changes when a call fails or succeeds, gas, and calls back into the contract.

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
