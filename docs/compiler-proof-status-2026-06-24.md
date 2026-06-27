# Compiler proof status

This document summarizes the current state of the compiler proof stack after the initial cleanup pass. It is a navigation/status aid, not a proof artifact.

## End-to-end shape

```text
Vyper source
  -- lowering -->
Venom IR
  -- optimization pipeline -->
Optimized Venom IR
  -- codegen -->
EVM bytecode
```

Top-level rollup:

- `vyperHolScript.sml` depends on compiler-related rollups/theories:
  - `venomPassesHol`
  - `venomAnalysisHol`
  - `venomPipelineCorrect`
  - `vyperLoweringHol`
  - `venomToAsmProps`
  - `asmToBytecodeProps`
  - `codegenCorrectness`

Lowering rollup:

- `lowering/vyperLoweringHolScript.sml` imports:
  - `moduleLowering`
  - `moduleLoweringProps`
  - `valueEncodingProofs`
  - `vyperCompiler`
  - `vyperLoweringCorrect`
  - `e2eCorrectness`

Notably not in the lowering rollup:

- `builtinTypeConvertProps` — incomplete/unwired type-conversion proof work
- `loweringMemSafetyProps` — separate memory-safety proof effort
- `evalCompiler*` — executable regression/evaluation fixtures

## High-level status

The proof architecture is present, but the end-to-end compiler proof is not closed.

- Lowering has many theorem statements and helper proofs, but core expression, statement, ABI, module dispatch, and top-level lowering correctness theorems are cheated.
- Pipeline correctness has generic composition infrastructure, but concrete optimization-level certification is not fully discharged in the e2e path.
- Codegen has substantial low-level infrastructure, but the core Venom-to-Asm, Asm-to-EVM, and final codegen correctness theorems remain cheated.

## Layer status table

| Layer | Main theories | Status | Main blockers / notes |
|---|---|---|---|
| Lowering definitions | `compileEnv`, `context`, `emitHelper`, `exprLowering`, `stmtLowering`, `moduleLowering`, `vyperCompiler` | Definitions present | May need update against current Python compiler before major proof work |
| Lowering expression props | `exprLoweringProps` | Partial; cheated core theorems | `compile_expr_correct`, name/binop/neg correctness, call-info monotonicity |
| Lowering statement props | `stmtLoweringProps` | Mostly statement skeletons; many cheats | `compile_stmt_correct`, `compile_stmts_correct`, assign/assert/return/if/for cases |
| ABI lowering | `abiEncoderProps` | Partial; cheated decode/encode/zero-pad theorems | Blocks ABI builtins and top-level argument/return correctness |
| Builtins | `builtinProps`, `builtinTypeConvertProps` | Partial; type conversion unwired | raw calls/create/send, ABI builtins, type conversion semantic theorem |
| Module lowering | `moduleLoweringProps` | Partial | selector dispatch, kwargs entry, runtime generation |
| Lowering top-level | `vyperLoweringCorrect` | Cheated top theorem | `vyper_to_venom_correct` |
| E2E bridge | `e2eCorrectness` | Partial; several cheats | EVM correspondence, call-result bridge, revert-state unchanged, O2 pipeline instance |
| Pipeline framework | `venomPipeline`, `venomPipelineCorrect` | Generic composition present | Concrete pass correctness/optimization-level instantiation not fully connected |
| Venom→Asm codegen | `venomToAsmProps`, `genBlockSim` and helpers | Substantial infra, core sim cheated | instruction/block/function simulation; `genBlockSim` has local cheated cases |
| Asm→EVM bytecode | `asmToBytecodeProps`, `asmBytecodeSim`, `evmStepSim` | Partial; top sim cheated | missing/needed preconditions around calls and single-context execution |
| Codegen top-level | `codegenCorrectness` | Cheated final theorems | `codegen_fn_correct`, `codegen_correct` |
| Lowering memory safety | `loweringMemSafety*` | Separate side effort | top `lowering_memory_safe` remains cheated; not in main rollup |
| Evaluation fixtures | `evalCompiler*` | Build-checked regression fixtures | Not correctness proofs; currently under `lowering/defs` |

## Current cheats by theory

### Lowering

#### `lowering/abiEncoderPropsScript.sml`

Cheated theorem areas:

- `compile_abi_decode_static_correct`
- `compile_abi_encode_to_buf_correct`
- `compile_abi_zero_pad_correct`

#### `lowering/builtinPropsScript.sml`

Cheated theorem areas:

- `compile_raw_call_correct`
- `compile_send_correct`
- `compile_raw_create_correct`
- `lower_abi_encode_correct`
- `lower_abi_decode_correct`

`compile_type_convert_correct` was moved to `builtinTypeConvertPropsScript.sml` for build-time reasons.

#### `lowering/builtinTypeConvertPropsScript.sml`

Cheated theorem:

- `compile_type_convert_correct`

This theory is currently not imported by the lowering rollup.

#### `lowering/emitHelperPropsScript.sml`

Cheated compile-state and label-space invariants:

- `fresh_label_output_inj`
- `compile_state_ok_initial`
- `compile_state_ok_emit_op`
- `compile_state_ok_emit_void`
- `compile_state_ok_emit_inst`
- `fresh_label_produces_external`
- `compile_state_ok_fresh_var`
- `compile_state_ok_fresh_id`
- `compile_state_ok_new_block`
- `label_external_mono`

These are likely important cleanup/proof targets because many lowering proofs rely on compile-state hygiene.

#### `lowering/exprLoweringPropsScript.sml`

Cheated theorem areas:

- `compile_expr_correct`
- `compile_name_correct`
- `compile_binop_correct`
- `compile_neg_correct`
- `compile_expr_ci_mono`

#### `lowering/stmtLoweringPropsScript.sml`

Cheated statement correctness theorem areas:

- `compile_stmt_correct`
- `compile_stmts_correct`
- `compile_expr_stmt_correct`
- `compile_annassign_correct`
- `compile_assign_name_correct`
- `compile_assert_correct_true`
- `compile_assert_bare_correct_false`
- `compile_assert_reason_correct_false`
- `compile_return_none_external_correct`
- `compile_return_none_internal_correct`
- `compile_return_some_external_correct`
- `compile_return_some_internal_correct`
- `compile_if_correct`
- `compile_for_range_correct`

#### `lowering/moduleLoweringPropsScript.sml`

Cheated theorem areas:

- `compile_selector_dispatch_linear_correct`
- `compile_selector_dispatch_sparse_correct`
- `compile_entry_point_kwargs_correct`
- `compile_generate_runtime_correct`

#### `lowering/vyperLoweringCorrectScript.sml`

Cheated theorem:

- `vyper_to_venom_correct`

#### `lowering/e2eCorrectnessScript.sml`

Cheated theorem areas:

- `compile_vyper_evm_correspondence`
- `evm_correspondence_to_call_result`
- `evm_revert_state_unchanged`
- `o2_pipeline_ctx_pass_correct`

#### `lowering/proofs/loweringMemSafetyProofsScript.sml`

Cheated theorem:

- `lowering_memory_safe`

This is a separate side proof effort and is not currently imported by `vyperLoweringHol`.

### Codegen

#### `venom/codegen/venomToAsmPropsScript.sml`

Core cheated simulation theorems:

- `gen_inst_simulation`
- `gen_block_simulation`
- `gen_fn_simulation`

The file comments document missing/precondition obligations, including instruction well-formedness, operand bounds, label resolution, spill well-formedness, SSA freshness, PHI soundness, and stack-depth invariants.

#### `venom/codegen/asmToBytecodePropsScript.sml`

Cheated theorem:

- `asm_bytecode_sim`

Known issue: earlier statement is false without enough restrictions around asm calls and EVM context depth. See `docs/compiler-proof-drafts-and-counterexamples.md`.

#### `venom/codegen/codegenCorrectnessScript.sml`

Cheated theorem areas:

- `codegen_fn_correct`
- `codegen_correct`

#### `venom/codegen/proofs/genBlockSimScript.sml`

Cheated local proof areas include:

- `gen_inst_halt_sim`
- `gen_inst_abort_sim`
- `do_dup_poke_venom_asm_rel`

This file also contains substantial completed block/instruction simulation infrastructure.

### Pipeline

`venom/compiler/venomPipelineCorrectScript.sml` currently has no cheats after removal of the obsolete draft theory. It is best understood as generic framework infrastructure. The concrete end-to-end use is still blocked by cheated e2e/pipeline instantiation obligations such as `o2_pipeline_ctx_pass_correct`.

## Remaining side/unwired theories

| Theory | Location | Status |
|---|---|---|
| `builtinTypeConvertProps` | `lowering/builtinTypeConvertPropsScript.sml` | Incomplete/unwired type-conversion correctness proof |
| `loweringMemSafetyProps` | `lowering/loweringMemSafetyPropsScript.sml` | Separate memory-safety proof effort; not in lowering rollup |
| `evalCompiler` | `lowering/defs/evalCompilerScript.sml` | Compiler evaluation fixtures, not core defs |
| `evalCompilerBytecode` | `lowering/defs/evalCompilerBytecodeScript.sml` | Bytecode fixture comparison by EVAL |
| `fnPlanDecomp` | `venom/codegen/proofs/fnPlanDecompScript.sml` | Unwired but likely future infrastructure for `gen_fn_simulation` |
| `venomStepProps` | `venom/codegen/proofs/venomStepPropsScript.sml` | Small general semantics lemmas; currently unused |

## Navigation notes

### Lowering

Start with:

- definitions: `lowering/defs/`
- props/statements: `lowering/*PropsScript.sml`
- proof wrappers: `lowering/proofs/`
- top-level: `lowering/vyperLoweringCorrectScript.sml`, `lowering/e2eCorrectnessScript.sml`

Important rollup:

- `lowering/vyperLoweringHolScript.sml`

### Pipeline

Start with:

- `venom/compiler/venomPipelineScript.sml`
- `venom/compiler/venomPipelineCorrectScript.sml`

The pipeline proof framework composes pass correctness; it does not by itself prove every concrete pass correct.

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

Proof layers:

- stack/prefix/plan helpers under `venom/codegen/proofs/`
- block simulation: `genBlockSimScript.sml`
- top statements: `venomToAsmPropsScript.sml`
- asm/EVM: `asmToBytecodePropsScript.sml`, `asmBytecodeSimScript.sml`, `evmStepSimScript.sml`
- final: `codegenCorrectnessScript.sml`

## Suggested next planning questions

1. Should formal compiler definitions be updated to match current Python compiler behavior before attempting major proof repair?
2. Which target should be the next proof milestone?
   - lowering expression/statement correctness,
   - ABI correctness,
   - concrete pipeline O2 correctness,
   - codegen simulation,
   - or a smaller executable/regression story?
3. Should the repo be reorganized to separate:
   - definitions,
   - active proof statements,
   - completed proof libraries,
   - incomplete/unwired proof work,
   - executable regression fixtures?
4. Should `docs/compiler-proof-status.md` become the central status tracker, updated whenever cheats are closed or theorem statements change?
