# Compiler proof dependencies

This document tracks the dependency structure of the intended compiler correctness proof. It begins as a roadmap skeleton and should become a theorem-level dependency graph during statement stabilization.

Related documents:

- [`compiler-correctness-specification.md`](compiler-correctness-specification.md)
- [`compiler-definition-parity.md`](compiler-definition-parity.md)
- [`compiler-proof-roadmap.md`](compiler-proof-roadmap.md)
- [`compiler-proof-status.md`](compiler-proof-status.md)

## Classification of hypotheses

Every important hypothesis in a stage theorem should be classified as one of:

- **environmental** — supplied by the execution setting and not established by the compiler;
- **boundary** — validity of elaborated AST or frontend metadata at the formal compiler boundary;
- **produced** — established by the current compiler stage;
- **preserved** — assumed at input and proved to remain true at output;
- **consumed** — required by this stage and expected to be produced earlier.

This classification is intended to prevent codegen or e2e assumptions from silently becoming unproved compiler obligations.

## High-level dependency graph

```text
Pinned-definition parity
        |
        v
Compiler boundary + source/target observations
        |
        +-------------------------+
        |                         |
        v                         v
Lowering infrastructure      Codegen statement validation
        |                         |
        v                         v
Expression/statement/ABI     Stack-plan foundations
correctness                       |
        |                         v
        v                    Instruction/block/function sim
Module/runtime/deploy             |
correctness                       v
        |                    Asm-to-EVM nested-context sim
        v                         |
vyper_to_venom_correct            v
        |                    codegen_correct
        v                         ^
Minimal mandatory pipeline -------+
correctness + invariant preservation
        |
        v
Runtime/deployment e2e composition
```

The graph is not purely linear: lowering and codegen can proceed in parallel once their shared state relations and invariant interfaces are stable.

## Boundary obligations

Expected boundary facts include:

- elaborated AST validity;
- type/metadata consistency;
- module/import resolution consistency;
- storage and immutable layout consistency;
- selector and entry-point consistency;
- function reachability/ID consistency;
- compiler settings and EVM-version validity.

**Producer:** formal frontend work or theorem caller.

**Consumers:** lowering correctness and top-level e2e theorem.

A future `compiler_input_ok` predicate should package these facts.

## Lowering dependency groups

### Compile-state hygiene

Expected facts:

- fresh variables, labels, and instruction IDs;
- uniqueness of generated labels;
- valid current/finalized block structure;
- preservation by emission and block operations.

**Producer:** `emitHelperProps` and related infrastructure.

**Consumers:** expression, statement, module, and codegen-readiness proofs.

### Value/state correspondence

Expected facts:

- value encoding/decoding;
- variable correspondence;
- storage/transient-storage correspondence;
- memory/buffer correspondence;
- immutable and environment correspondence.

**Producer:** value encoding and lowering state-relation theories.

**Consumers:** expression, statement, ABI, call, and module proofs.

### Expression correctness

Depends on compile-state hygiene, value/state correspondence, builtin lemmas, and call-layout facts.

**Produces:** expression result correspondence, emitted-code simulation, state relation preservation, and compile-state invariants.

### Statement correctness

Depends on expression correctness and control-flow simulation helpers.

**Produces:** statement/list execution correspondence and preservation of lowering invariants.

### ABI correctness

Depends on value encoding, memory/buffer correspondence, and bounds/allocation facts.

**Produces:** calldata/argument and return/revert-data correspondence.

### Module correctness

Depends on statement correctness, ABI correctness, selector dispatch, function metadata, and runtime/deploy construction.

**Produces:** `vyper_to_venom_correct` and initial codegen-readiness facts.

## Mandatory pipeline dependency groups

For every mandatory pass, track two independent theorem families:

1. semantic preservation;
2. structural invariant preservation/production.

Expected invariants include:

- context/function well-formedness;
- label uniqueness and resolvability;
- SSA or the required post-SSA form;
- PHI placement/elimination conditions;
- call-layout consistency;
- allocation and memory-region properties;
- codegen readiness.

The composed pipeline theorem must produce every condition consumed by codegen. A semantically correct pipeline theorem alone is insufficient.

## Codegen dependency groups

### Stack-plan validity

Expected facts:

- plan stack relates to Venom variables/values;
- reordering and stack operations preserve that relation;
- stack depth stays in EVM bounds;
- spills are valid and separated from source-visible memory;
- labels and return points are fresh/resolvable.

**Consumers:** instruction and block simulation.

### Instruction simulation

Depends on opcode-specific Venom/EVM semantics and stack-plan validity.

`PARAM` requires a block/function-entry invariant and should not be forced into an unrestricted instruction-local theorem.

**Produces:** simulation for ordinary instruction steps under explicit local invariants.

### Block simulation

Depends on instruction simulation, PHI/parameter preparation, terminator semantics, and successor transfer.

**Produces:** block-entry to successor/exit correspondence.

### Function/context simulation

Depends on block simulation, function-plan decomposition, call layout, internal returns, and frame invariants.

**Produces:** Venom-to-assembly context simulation.

### Assembly-to-EVM simulation

Depends on:

- assembly/symbol-resolution correctness;
- opcode-step correspondence;
- program-counter and label relations;
- data-section addressing;
- call-frame and nested-context semantics;
- return/revert and state commit/rollback behavior.

A no-calls or single-context theorem may be a helper, but cannot discharge the final requested scope.

### Top-level codegen correctness

Depends on function/context simulation, assembly-to-EVM simulation, symbol resolution, data sections, and all codegen-readiness invariants.

**Produces:** EVM execution correspondence for generated runtime or deployment bytecode.

## Memory and allocation obligations

The exact dependency direction must be established rather than assumed. Candidate facts are:

- compile-time ALLOCA sizes agree with runtime allocation records;
- ALLOCA output variables contain allocation bases;
- derived pointers stay in their regions;
- ABI and temporary buffers are valid;
- codegen spill regions are disjoint from program memory;
- mandatory transformations preserve these properties.

Likely producers are lowering correctness plus allocation/codegen setup. Likely consumers are stack-plan simulation, memory-op simulation, and e2e composition.

The existing `lowering_memory_safe` theorem should be used only if its final statement matches this interface.

## End-to-end dependencies

### Runtime external-call correctness

Requires:

- valid compiler input;
- lowering correctness;
- minimal-pipeline correctness and invariant preservation;
- runtime codegen correctness;
- source/EVM observation relation;
- external-contract assumptions;
- gas/fuel assumptions.

### Deployment correctness

Additionally requires:

- constructor lowering correctness;
- runtime-bytecode embedding/data-section correctness;
- immutable handling;
- deployed-code return correspondence;
- deployment revert/failure correspondence.

### Nested/multi-contract correctness

Requires a compositional external-call specification or closed-world assumption connecting callees' source and EVM behavior. Reentrancy and nested context return/revert behavior must be covered by the selected call relation.

## Known dependency hazards

- `PARAM` changes Venom variables without emitted assembly and therefore depends on function-entry stack conditions.
- Earlier `asm_bytecode_sim` statements omitted call and context-depth requirements.
- Allocation well-formedness alone does not connect lowered allocations to runtime pointer values.
- Semantic pass correctness does not by itself establish codegen-ready structural invariants.
- A parameterized lowering wrapper may hide frontend metadata obligations unless they are packaged at the boundary.

## Maintenance format

As statements stabilize, add a table for each top-level theorem:

| Theorem | Theory | Status | Consumes | Produces | Blockers |
|---|---|---|---|---|---|

Use exact theorem and predicate names. Avoid listing implementation helpers unless they represent a genuine cross-stage dependency.
