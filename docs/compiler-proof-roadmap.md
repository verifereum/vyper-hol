# Compiler correctness roadmap

This document describes the planned work, dependencies, milestones, and parallel work packages for the compiler correctness proof. It deliberately does not estimate calendar time.

Related documents:

- [`compiler-proof-status.md`](compiler-proof-status.md) — current proof status and cheat inventory
- [`compiler-definition-parity.md`](compiler-definition-parity.md) — parity with the pinned Python compiler
- [`compiler-correctness-specification.md`](compiler-correctness-specification.md) — compiler boundary and intended theorem family
- [`compiler-proof-dependencies.md`](compiler-proof-dependencies.md) — proof and invariant dependency structure
- [`compiler-proof-drafts-and-counterexamples.md`](compiler-proof-drafts-and-counterexamples.md) — known false statements and historical lessons

## Goal and initial scope

The intended correctness architecture is:

```text
Elaborated Vyper AST and metadata
  -- lowering correctness -->
Venom IR
  -- mandatory pipeline correctness -->
Codegen-ready Venom IR
  -- codegen correctness -->
EVM bytecode
  -- execution correspondence -->
Source-level observable behavior
```

The first end-to-end target should cover the full compiler functionality represented at the chosen formal boundary, including deployment, runtime execution, calls, and nested EVM contexts. It should use only the transformations mandatory for code generation. Optional O2/O3/Os optimization certification should be layered on later.

`VYPER_PIN` is the sole authoritative upstream compiler revision. Per-file source annotations should identify Python paths and symbols, but must not establish independent revision pins.

## Phase 0 — Fix the target and theorem boundary

### 0.1 Use the repository-wide Vyper pin

- Read the target revision from `VYPER_PIN`.
- Use that revision for compiler definitions, language-test exports, generated AST JSON, bytecode fixtures, and downstream tooling.
- Replace or qualify stale per-file commit annotations so they cannot be mistaken for separate targets.

### 0.2 Define the trusted front-end boundary

Specify which compiler inputs are formal and which are trusted or supplied by the elaborated frontend. In particular, decide how the proof treats:

- parsing and JSON import;
- type checking and semantic analysis;
- module and import resolution;
- storage and immutable layouts;
- function metadata and reachability;
- selectors and entry-point metadata;
- compiler settings and EVM version.

The initial theorem is expected to begin with an elaborated HOL AST plus explicit metadata assumptions, rather than raw Vyper source text.

### 0.3 Define the initial pipeline configuration

- Identify the smallest pinned-compiler pipeline accepted by codegen.
- Include mandatory normalization or lowering passes.
- Exclude optional optimizations from the first theorem.
- Give this pipeline a dedicated formal name rather than treating it as an accidental subset of O2.

### 0.4 Confirm execution scope

The theorem family should include:

- runtime and deployment bytecode;
- internal and external calls;
- nested EVM contexts;
- success, halt, return, and revert behavior;
- externally visible state effects.

## Phase 1 — Compiler-definition parity

This phase answers which pinned Python compiler is represented by the HOL definitions.

### 1.1 Build the parity inventory

For each relevant definition, record:

- Python source path and symbol;
- HOL theory and definition;
- parity status;
- intentional abstraction, if any;
- required update;
- effect on theorem statements and existing proofs.

Use the statuses defined in [`compiler-definition-parity.md`](compiler-definition-parity.md).

### 1.2 Audit the formal compiler boundary

Compare Python's module-driven compiler API with the parameterized HOL lowering API. Classify every supplied item—selectors, entry information, function lists, dispatch tables, layouts, IDs, reachability, and data sections—as:

1. formally computed;
2. supplied under an explicit relation to frontend output; or
3. trusted at the theorem boundary.

Package these conditions in a coherent compiler-input validity predicate rather than scattering them across top-level theorems.

### 1.3 Audit lowering

Audit:

- compile environment and emission;
- values, pointers, and locations;
- expressions and arithmetic;
- assignments and evaluation order;
- statements and control flow;
- internal and external calling conventions;
- builtins and type conversions;
- ABI encoding and decoding;
- selector dispatch and kwargs;
- module/function reachability;
- runtime and deployment generation;
- data sections and metadata.

### 1.4 Audit Venom IR semantics

Check instructions and operand order, labels and entry semantics, parameters and returns, internal invocation, allocations, effects, exceptional behavior, calls, and well-formedness assumptions.

### 1.5 Audit the mandatory pipeline

For every pass needed before codegen:

- compare HOL and Python definitions;
- specify required and produced invariants;
- identify semantic-correctness coverage;
- decide whether it belongs conceptually to lowering, the pipeline, or codegen preparation.

Inventory optional O2/O3/Os passes separately; they do not block the first end-to-end theorem.

### 1.6 Audit codegen

Audit stack planning, parameter preparation, PHI handling, spills, calls and returns, instruction lowering, labels and symbols, data sections, deploy/runtime assembly, fork assumptions, and bytecode metadata.

### 1.7 Parity milestone exit criteria

- One authoritative pinned revision.
- A complete correspondence matrix for the first e2e path.
- No unresolved `unknown` entries on that path.
- All intentional abstractions documented.
- A definition-update backlog with proof impact noted.
- A specified formal compiler boundary.
- A specified minimal mandatory pipeline.

## Phase 2 — Stabilize semantics and theorem statements

No major proof repair should precede confidence that the principal statements are true and composable.

### 2.1 Define observations

Specify source and EVM observations, including result status, return/revert data, persistent and transient storage, balances/account state, logs, created contracts, and other externally visible effects.

### 2.2 Align simulation relations

Stabilize the relations between:

- Vyper and Venom states/results;
- Venom and assembly states/results;
- assembly and EVM states/results;
- EVM execution and source-level call results.

### 2.3 Stabilize invariant families

Expected families include:

- compile-state freshness and label uniqueness;
- Venom well-formedness;
- SSA and PHI correctness;
- function parameter and return conventions;
- stack-plan validity and stack-depth bounds;
- operand bounds and spill-region separation;
- label resolution and codegen readiness;
- call-layout correctness;
- memory/allocation correspondence.

### 2.4 Resolve known statement defects

Explicitly account for the documented issues involving `PARAM`, operand order, asm calls, nested EVM contexts, and ALLOCA/pointer correspondence. Do not retain a local theorem shape if the needed invariant only exists at block or function scope.

### 2.5 Statement-stability exit criteria

Produce the dependency structure described in [`compiler-proof-dependencies.md`](compiler-proof-dependencies.md), with each important hypothesis classified as:

- produced by an earlier compiler stage;
- preserved by a transformation;
- consumed by a later stage; or
- an environmental assumption.

## Phase 3 — Implement parity corrections

Apply definition updates before repairing proofs tied to stale definitions. Suggested order:

1. shared Venom syntax and semantics;
2. lowering environment and calling conventions;
3. expression and statement lowering;
4. ABI and builtins;
5. module/runtime/deploy lowering;
6. mandatory pipeline;
7. stack planning and codegen;
8. fixtures and documentation.

For every update, record the pinned Python source mapping and classify invalidated theorems. Avoid preserving obsolete definitions solely to minimize proof churn.

## Phase 4 — Lowering correctness

### 4.1 Compilation infrastructure

Prove freshness, uniqueness, label-space monotonicity, block creation, initial-state validity, and preservation by emission operations.

### 4.2 Value and state correspondence

Establish reusable correspondence for source values, words and buffers, locals, storage, transient storage, immutables, memory pointers/allocations, and transaction/environment fields.

### 4.3 Expression correctness

Develop feature-specific results for literals/names, arithmetic, comparisons, conversions, attributes/subscripts, compound values, builtins, and calls. Assemble `compile_expr_correct` from these results.

### 4.4 Statement correctness

Develop results for declarations, assignments, assertions, reverts, returns, conditionals, loops, logs/events, mutation, and internal-call control flow. Assemble the statement-list theorem from these cases.

### 4.5 ABI and call boundaries

Prove calldata decoding, argument layout, kwargs/defaults, return encoding, revert payloads, ABI builtins, and external-call result decoding.

### 4.6 Module correctness

Prove selector dispatch, fallback behavior, reachability assumptions, runtime generation, deployment generation, and data-section correctness.

### 4.7 Lowering milestone

Close `vyper_to_venom_correct` for the pinned and parity-audited lowering definition.

## Phase 5 — Mandatory pipeline correctness

### 5.1 Specify the pipeline

Define the named minimal pipeline and its required analyses/configuration.

### 5.2 Certify mandatory transformations

For each transformation, separate:

- semantic preservation;
- well-formedness preservation;
- production or preservation of codegen-readiness invariants.

### 5.3 Compose the pipeline

Instantiate the generic pipeline framework to obtain a concrete minimal-pipeline theorem.

### 5.4 Add optional pipelines

After the first e2e result, certify O2, O3, Os, and useful custom pass configurations as interchangeable pipeline theorems.

## Phase 6 — Codegen correctness

### 6.1 Stack-plan foundations

Prove stack-operation semantics, variable/value correspondence, reorder/dup/swap/poke correctness, spill correctness, and stack-depth bounds.

### 6.2 Instruction simulation

Handle pure operations, memory/storage, control flow, environment operations, calls/creation, halting/reverting, and parameters/internal returns. Treat `PARAM` at the block or function boundary if that is where its invariant is available.

### 6.3 Block simulation

Close local `genBlockSim` cases and establish entry-stack, successor-transfer, PHI/parameter, and terminator invariants.

### 6.4 Function and context simulation

Prove function entry, internal calls/returns, stack-frame layout, context dispatch, and nested execution, using or replacing `fnPlanDecomp` as appropriate.

### 6.5 Assembly-to-EVM simulation

The requested scope includes calls and nested contexts. Either extend assembly semantics to model them or use a justified atomic call relation. Prove opcode, program-counter, label, call-frame, return/revert, and data-section correspondence.

### 6.6 Codegen milestone

Close corrected forms of:

- `gen_inst_simulation`;
- `gen_block_simulation`;
- `gen_fn_simulation`;
- `asm_bytecode_sim`;
- `codegen_fn_correct`;
- `codegen_correct`.

## Phase 7 — Discharge memory-safety obligations

Do not require the existing broad memory-safety theorem merely because it exists. Instead:

1. enumerate the exact memory hypotheses consumed by codegen;
2. prove lowering establishes them;
3. prove mandatory passes preserve them;
4. package them as part of codegen readiness.

Likely obligations concern ALLOCA sizes and bases, pointer bounds, spill/program-memory separation, and ABI/temporary-buffer regions. Derive a broader `lowering_memory_safe` theorem only if useful.

## Phase 8 — End-to-end composition

### 8.1 Runtime correctness

Compose lowering, mandatory pipeline, codegen, and EVM/source-result correspondence.

### 8.2 Deployment correctness

Cover constructor execution, runtime-bytecode embedding, immutables, deployed-code return, and deployment failure.

### 8.3 Nested-call correctness

Support calls between compiled contracts, calls to externally specified EVM contracts, and reentrant calls under explicit assumptions.

### 8.4 Final theorem family

Prefer precise composable theorems:

- runtime external-call correctness;
- deployment correctness;
- minimal-pipeline compiler correctness;
- optional-pipeline corollaries;
- multi-contract/system corollaries where feasible.

## Parallel work packages

After phases 0–2 stabilize shared interfaces, work can divide into:

- **Track A:** lowering, ABI, and module correctness;
- **Track B:** mandatory and optional pipeline certification;
- **Track C:** stack planning and Venom-to-assembly simulation;
- **Track D:** assembly-to-EVM simulation, calls, and nested contexts;
- **Track E:** shared invariants and end-to-end integration.

For a single expert, use the phase ordering above, but periodically develop a narrow vertical slice to test whether assumptions genuinely compose.
