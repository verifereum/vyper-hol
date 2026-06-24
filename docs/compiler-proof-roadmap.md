# Compiler proof roadmap

This is a high-level roadmap for continued work on compiler correctness. For detailed current cheat/status information, see [`compiler-proof-status.md`](compiler-proof-status.md). For notes about stale draft theories and historical counterexamples, see [`compiler-proof-drafts-and-counterexamples.md`](compiler-proof-drafts-and-counterexamples.md).

## Intended correctness architecture

```text
Vyper AST/source semantics
  -- lowering correctness -->
Venom IR semantics
  -- Venom optimization pipeline correctness -->
Optimized Venom IR semantics
  -- codegen correctness -->
EVM bytecode semantics
```

There are three main proof legs plus a top-level composition/glue layer:

1. **Lowering:** Vyper AST/source semantics to Venom IR execution.
2. **Pipeline:** semantics-preserving Venom-to-Venom transformations.
3. **Codegen:** optimized Venom IR to EVM bytecode execution.
4. **E2E composition:** reconcile the theorem statements, preconditions, ABI interface, observable-result relations, gas/call-frame assumptions, and pipeline configuration.

## Current high-level status

The architecture is present, but end-to-end compiler correctness is not closed.

- **Lowering** is a major open area. Definitions and theorem statements exist, but core expression, statement, ABI, module dispatch, builtin, and top-level lowering correctness theorems remain cheated.
- **Pipeline/pass correctness** has the most mature reusable framework. Generic simulation/composition infrastructure exists, and several passes have proof work, but the concrete optimization-level instance used by the e2e compiler story is not fully discharged.
- **Codegen** has substantial low-level infrastructure, especially around stack plans, asm execution, and asm/EVM stepping, but the central Venom-to-Asm, Asm-to-EVM, and final codegen correctness theorems remain cheated.
- **Top-level e2e** is best viewed as scaffolding until the three legs provide closed theorems with compatible assumptions.

## Before major proof repair: compiler-definition parity

Before investing heavily in proof repair, audit and update the formal compiler definitions against the intended Python compiler version. Some HOL files record different upstream source anchors, and recent upstream Vyper commits include Venom/compiler bug fixes.

See [`compiler-definition-parity.md`](compiler-definition-parity.md).

A productive workflow is likely:

1. Choose/pin an exact upstream Vyper commit.
2. Audit the formal lowering, pipeline, and codegen definitions against that commit.
3. Update definitions and executable fixtures as needed.
4. Only then prioritize closing proof gaps.

## Suggested work order

### 1. Pin and audit compiler definitions

This should probably precede large proof work. It answers: “Which compiler are we proving correct?”

Key outputs:

- chosen target upstream commit,
- per-component parity checklist,
- list of intentional HOL/Python differences,
- executable fixture updates if outputs change.

### 2. Stabilize theorem statements and assumptions

Before proving large results, make sure statement shapes are true and composable.

Key areas:

- `vyper_to_venom_correct` interface and state/result relation,
- `gen_inst_simulation`, `gen_block_simulation`, `gen_fn_simulation`,
- `asm_bytecode_sim` preconditions around calls/context depth,
- `codegen_correct` gas/call-frame assumptions,
- e2e observable result relation.

### 3. Lowering proof milestones

Likely milestones:

- compile-state/label hygiene in `emitHelperProps`,
- expression lowering core cases,
- statement lowering core cases,
- ABI encode/decode correctness,
- module dispatch/runtime generation,
- top-level `vyper_to_venom_correct`.

### 4. Codegen proof milestones

Likely milestones:

- close remaining local cases in `genBlockSim`,
- use/wire future function-plan infrastructure such as `fnPlanDecomp`,
- strengthen/fix top-level Venom-to-Asm statements,
- strengthen/fix Asm-to-EVM statement preconditions,
- close `codegen_fn_correct` and `codegen_correct`.

### 5. Pipeline instantiation milestones

The generic framework is useful, but final compiler correctness needs the actual configured pipeline theorem.

Likely work:

- identify the target optimization level(s),
- prove or assume explicitly each pass-correctness obligation,
- close `o2_pipeline_ctx_pass_correct` or replace it with a better named/configured theorem,
- track SSA/WF preservation obligations separately from semantic simulation obligations.

## Navigation guide

### Lowering

Definitions:

- `lowering/defs/compileEnvScript.sml`
- `lowering/defs/contextScript.sml`
- `lowering/defs/emitHelperScript.sml`
- `lowering/defs/exprLoweringScript.sml`
- `lowering/defs/stmtLoweringScript.sml`
- `lowering/defs/moduleLoweringScript.sml`
- `lowering/defs/vyperCompilerScript.sml`

Proof/property layers:

- `lowering/emitHelperPropsScript.sml`
- `lowering/exprLoweringPropsScript.sml`
- `lowering/stmtLoweringPropsScript.sml`
- `lowering/abiEncoderPropsScript.sml`
- `lowering/builtinPropsScript.sml`
- `lowering/builtinTypeConvertPropsScript.sml`
- `lowering/moduleLoweringPropsScript.sml`
- `lowering/vyperLoweringCorrectScript.sml`
- `lowering/e2eCorrectnessScript.sml`

Side efforts/fixtures:

- `lowering/loweringMemSafetyPropsScript.sml`
- `lowering/proofs/loweringMemSafetyProofsScript.sml`
- `lowering/defs/evalCompilerScript.sml`
- `lowering/defs/evalCompilerBytecodeScript.sml`

### Pipeline

- `venom/compiler/venomPipelineScript.sml`
- `venom/compiler/venomPipelineCorrectScript.sml`
- individual pass definitions/proofs under `venom/passes/`

### Codegen

Definitions:

- `venom/codegen/defs/stackModelScript.sml`
- `venom/codegen/defs/stackPlanTypesScript.sml`
- `venom/codegen/defs/stackPlanOpsScript.sml`
- `venom/codegen/defs/stackPlanGenScript.sml`
- `venom/codegen/defs/planExecScript.sml`
- `venom/codegen/defs/asmIRScript.sml`
- `venom/codegen/defs/asmSemScript.sml`
- `venom/codegen/defs/symbolResolveScript.sml`
- `venom/codegen/defs/codegenScript.sml`

Proofs/statements:

- `venom/codegen/proofs/genBlockSimScript.sml`
- `venom/codegen/proofs/fnPlanDecompScript.sml`
- `venom/codegen/venomToAsmPropsScript.sml`
- `venom/codegen/asmToBytecodePropsScript.sml`
- `venom/codegen/codegenCorrectnessScript.sml`

## Organization principles for future cleanup

Prefer making intent explicit before moving many files:

- Mark active proof chain vs side/unwired work.
- Keep dated status documents for historical accuracy.
- Use stable index docs for discoverability.
- Avoid large proof-file splits until theorem statements and compiler-definition parity are stable.
