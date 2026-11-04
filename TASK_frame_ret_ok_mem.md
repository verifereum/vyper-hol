# TASK: S3: the external frame's returns halt memory-safely (external_frame_ret_ok_mem)

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: project root (theorem in `lowering/loweringMemCorrectScript.sml`, theory `loweringMemCorrect`)

## Theorem Statement (FROZEN)

```sml
Theorem external_frame_ret_ok_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    frame_ret_ok_mem NONE unit.cu_context func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es r. T) cenv ret
```

It is currently proved by `cheat` in `lowering/loweringMemCorrectScript.sml`.
Replace that cheat with a real proof.

**Do not modify this statement, or any definition it uses.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THE MAIN PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Helper lemmas go in new theory files under lowering/,
 * imported by loweringMemCorrect, each built before the
 * main proof.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build loweringMemCorrectTheory` passes with zero failures, and `external_frame_ret_ok_mem` and every new helper have no CHEAT. The other admissions in that file (`body_stmts_sim_mem`, `lower_vyper_runtime_unit_ptr_taint`, `external_entry_value_revert_mem`, `external_entry_reaches_body_mem`) stay as they are; another run is proving `external_entry_value_revert_mem` and `external_entry_reaches_body_mem` in parallel. Don't remove or add any cheat.
2. No duplicate or near-duplicate lemmas: search the `.sig` files under `.holbuild` and `lowering/*.sml`, `venom/**/*.sml` before stating a new one, and reuse what exists.
3. No new axioms, no new premises on the frozen theorem, no changes to any definition (nothing under `lowering/defs/`, `semantics/`, `venom/` definitions, `lowering/bodyMemoryDefsScript.sml`, `lowering/bodySimScript.sml`, `lowering/stmtSimScript.sml` definitions).
4. Put new helper lemmas in new theory files under `lowering/` named for their content, e.g. `externalReturnMemScript.sml`, imported by `loweringMemCorrect` (add them to its `Ancestors`); register nothing else. Helpers that no other theory uses are `[local]`. Proofs stay under 50 lines each.
5. No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`. No tactic-timeout changes: every step must fit the default 2.5 s.
6. Commits: commit only `.sml` files under `lowering/` (and this TASK file at the project root); never commit `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*` or tool output. End every commit message with these two lines:
   ```
   Bot: opus (Claude Opus 5.5)
   Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
   ```

**If the theorem is false as stated:** produce a concrete counterexample (program, call, state), state the tightest sufficient fix, and stop. Do not weaken the statement.

## Build

```
cd <worktree root, the directory with holproject.toml>
holbuild --max-heap 8000 -j4 build loweringMemCorrectTheory
```

## Background

- What it says: in the selected external function's frame (no caller return buffer, `d = NONE`; the result relation `RetQ` is trivial), every `Return eo` statement, after its returned expression's memory simulation, halts memory-safely (`frame_ret_ok_mem`, `lowering/bodyMemoryDefsScript.sml`; with `RetQ = T`, `stmt_frag_mem`'s exit disjunct needs a halting run (`exit_result`) that is `mem_safe_run` from the start state).
- Lowering of `Return` in an external frame (`compile_stmt`, `lowering/defs/stmtLoweringScript.sml`, `ce_return_pc = NONE`): `Return NONE` is a STOP; `Return (SOME e)` lowers the value, normalizes it into a fresh buffer when its type differs from the return type (widening: `needs_normalize`, `compile_store_memory_typed`), then `compile_external_return`: raw return, word (`ALLOCA 32; MSTORE; RETURN`), static aggregate (`ALLOCA; MCOPY; RETURN`, `AbiCopy`), or the ABI encoder into a fresh buffer (`compile_abi_encode_to_buf`, for dynamic types: `AbiBytestring`, `AbiDynArray`, `AbiComplex`, with loops and scratch ALLOCAs).
- Proved memory leaves exist for STOP, word, static copy and raw returns. The ABI encoder has S1 correctness (`compile_abi_encode_to_buf_correct`, `lowering/abiEncoderPropsScript.sml`, over the real recursive CFG) but no memory proof; the normalize step has none either. `frame_ret_ok_mem` quantifies over any `eo` that `type_stmt` accepts at the return type, so widened returns are in scope.
- The S1 `compile_external_return_abi_frag` (`lowering/loweringHaltScript.sml`) needs every fragment allocation id fresh in `s.vs_allocas`, which doesn't follow from `stmt_state_rel`/`alloca_history` for a return inside a loop; the S3 leaves use the site-size clause of `stmt_state_rel` instead (see `lowering/exprLoweringPropsScript.sml`, `alloca_room`).
- Memory safety: `mem_safe_run`, `mem_safe_blocks`, `mem_safe_block`, `mem_safe_step` (`venom/compiler/memSafeRunScript.sml`): every instruction executed reads and writes memory below the allocation frontier `vs_alloca_next` (`inst_mem_below_frontier`, `lowering/instMemFrontierScript.sml`), or is a revert forward (`inst_mem_ok_in_fn`, `unitTransformDefs`). `mem_safe_blocks` spends one fuel per block entered; `mem_safe_run_all_fuel`, `mem_safe_blocks_run`, `mem_safe_run_inst_seq` are the unfolding lemmas.
- The proved composition that consumes this theorem is `lower_vyper_runtime_unit_run_mem_safe` in the same file: read it to see exactly how the theorem is used.
- The theorem is the memory twin of S1's `external_frame_ret_ok` in `lowering/loweringRuntimeCorrectScript.sml`. That S1 lemma is itself still an admission (cheat) and gives no information about memory, so it is no shortcut; you may read its comment for intent.

## Domain Constraints

- Follow the lowering as defined; don't assume a supported subset narrower than `supported_program` gives.
- Stage lemmas stay generic: nothing here may fix the O1 finalizer or pass policy.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Memory-safe run defs and unfolding | `venom/compiler/memSafeRunScript.sml` | `mem_safe_run`, `mem_safe_blocks`, `mem_safe_blocks_run`, `mem_safe_run_all_fuel` |
| Per-opcode frontier facts | `lowering/instMemFrontierScript.sml` | `below_frontier_<OPC>`, `below_frontier_no_ranges` |
| Memory fragment judgment | `lowering/fragExecMemScript.sml` | `frag_exec_mem`, `run_inst_seq_mem_ok`, `frag_exec_mem_run_inst_seq`, `mem_safe_run_inst_seq`, `frag_exec_mem_assert_fail`, `frag_exec_mem_seq` |
| Allocation footprints | `lowering/allocaFootprintScript.sml`, `venom/proofs/allocaHistoryScript.sml` | ALLOCA at a site, `alloca_next_valid`, `alloca_history` and its step/jump lemmas |
| Entry/halt memory leaves (proved) | `lowering/entryHaltMemScript.sml`, `lowering/rawReturnMemScript.sml` | return none/STOP, word return, static copy return, raw return, static argument decode (`entry_decode_arg_mem_ok`) |
| Body memory judgments | `lowering/bodyMemoryDefsScript.sml` | `stmt_frag_mem`, `frame_ret_ok_mem`, `expr_sim_mem`, `return_buf_frame` |
| S1 fragment framework | `lowering/fragExecScript.sml`, `lowering/stmtSimScript.sml`, `lowering/bodySimScript.sml` | `frag_exec`, `stmt_frag`, `stmt_state_rel`, `stmt_exit`, `exit_result` |
| The lowering | `lowering/defs/moduleLoweringScript.sml`, `lowering/defs/stmtLoweringScript.sml`, `lowering/defs/abiEncoderScript.sml`, `lowering/defs/vyperCompilerScript.sml`, `lowering/compileVyperScript.sml` | `compile_generate_runtime`, `compile_external_fn_bodies`, `compile_entry_checks`, `compile_register_positional_args`, `compile_guarded_body`, `compile_external_return`, `compile_abi_encode_to_buf`, `compile_abi_decode_to_buf`, `run_lowering`, `extract_context_with_internals` |
| Supported subset | `lowering/supported/` | `supported_program`, `supported_place_type` |
| Vyper reference at VYPER_PIN | `alan-ref/vyper/vyper/codegen_venom/` | the Python lowering the HOL lowering follows |
| Encoder correctness (S1) | `lowering/abiEncoderPropsScript.sml`, `lowering/abiEncoder*Script.sml` (`abiEncoderMemoryScript.sml`, `abiEncoderWritesScript.sml`, `abiEncoderBufferFrameScript.sml`) | `compile_abi_encode_to_buf_correct` and its frame/writes lemmas |
| Return sequences (S1) | `lowering/loweringHaltScript.sml`, `lowering/stmtSimReturnScript.sml`, `lowering/retAbiPlanPropsScript.sml`, `lowering/vyperLoweringCorrectScript.sml` | `compile_external_return_*`, `external_return_*_result_rel`, return ABI plan facts, `external_return_buffer_ok` |
| Typed memory store (normalize) | `lowering/defs/exprLoweringScript.sml`, `lowering/exprSim*Script.sml` | `compile_store_memory_typed` and its S1 lemmas |

## Notes

- Weakly frozen: any helper lemma you introduce may be restated freely; only the theorem above is frozen.
- Two sibling runs prove the other two admissions of `loweringMemCorrect` in other worktrees; their helpers get merged with yours later, so give your helper theories distinct, content-based names.
