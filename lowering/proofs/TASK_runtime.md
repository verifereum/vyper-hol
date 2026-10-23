# TASK: prove compile_generate_runtime_shape

## Meta
Status: planned
Priority: P1
Created: 2026-10-23
Location: lowering/proofs

## Theorem Statement (FROZEN)

```sml
Theorem compile_generate_runtime_shape:
  !selectors external_fns internal_fns fallback_fn bucket_count
   fn_metadata_bytes dense_buckets entry_info st1.
    compile_generate_runtime selectors external_fns internal_fns fallback_fn
      Linear bucket_count fn_metadata_bytes dense_buckets entry_info
      (initial_compile_state "__entry") = ((), st1) /\
    EVERY (\(sel, lbl, z). isPREFIX "fn_" lbl) selectors /\
    EVERY external_fn_shape_ok external_fns /\
    fallback_shape_ok fallback_fn /\
    EVERY internal_fn_shape_ok internal_fns ==>
    shape_state st1 /\
    ?entry_blocks segs.
      all_blocks st1 = entry_blocks ++ FLAT segs /\
      entry_blocks <> [] /\ (HD entry_blocks).bb_label = "__entry" /\
      EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) entry_blocks)) /\
      EVERY (\bb. EVERY (lowered_inst_ok F) bb.bb_instructions)
        entry_blocks /\
      LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs
```

The definitions it uses are in `lowering/proofs/loweringShapePropsScript.sml` (side conditions: `expr_shape_root`, `cenv_shape_ok`, `value_shape_ok`, `loop_ctx_shape_ok`, `*_fn_shape_ok`, `internal_segment_ok`, `internal_name_ok`, ...) and `lowering/proofs/loweringShapeDefsScript.sml` (`shape_step`, `shape_state`, `plain_operand`, `label_or_plain`, `compiler_label`, `lowered_inst_ok`, ...). The comment directly above the theorem in the script says what it is for.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `compile_generate_runtime_shape` in `lowering/proofs/loweringShapePropsScript.sml` has a proof with no `cheat`, and `holbuild build loweringShapePropsTheory` passes under the default 2.5 s per-step tactic timeout.
2. The only cheats left in the file are the other lemmas listed under Domain Constraints; no new cheat anywhere.
3. No duplicate or near-duplicate helper lemmas.

**If the theorem is false as stated:** produce a HOL4 counterexample (e.g. `EVAL` on a concrete state/expression), state the tightest sufficient fix, and stop. Do not weaken or otherwise change the statement.

## Build

```
holbuild -j1 build loweringShapePropsTheory
```

Run from the project root (the directory with `holproject.toml`).

## Background

vyper-hol lowers Vyper to Venom IR. `o1_source_unit_ok` (`venom/compiler/unitShapeDefsScript.sml`) is the shape the O1 pipeline needs from the raw lowering: allowed opcodes only, instruction shape, `GAS`/return-PC outputs used only where `opaque_use_ok` allows, no `STOP`/`RETURN` in internal functions, no `RET`/`PARAM` in entry code, jump labels that exist. `loweringShapeProps` proves `o1_source_unit_ok` of the lowered unit (`lower_vyper_runtime_unit_source_unit_ok_names`) from generator lemmas, of which this is one. The framework in `loweringShapeDefs` is a Hoare-style judgment `shape_step internal LP P m Q` over the compile monad, with rules for bind/return/frame/consequence and every emit primitive.

## Domain Constraints

- Follow `AGENTS.md` at the project root (proof style, no `TRY`/`ORELSE` around `metis_tac` or other search, never raise the tactic timeout, no interactive `g`/`e` sessions).
- Do not edit the compiler: nothing under `lowering/defs/`, `lowering/supported/`, `venom/` or `semantics/` changes.
- Do not edit `loweringShapeDefsScript.sml`, any definition in `loweringShapePropsScript.sml`, or any other theorem's statement.
- These other lemmas in the same file are cheated and are being proved separately; use their statements freely but do not prove or edit them: `loc_shape_ok_mono`, `cenv_shape_ok_stable`, `value_shape_ok_stable`, `cenv_static_ok_shape_ok`, `compile_expr_shape`, `unwrap_value_shape`, `declare_local_shape`, `declare_stmt_local_shape`, `compile_stmt_shape`, `compile_selector_dispatch_linear_shape`, `compile_external_fn_bodies_shape`, `compile_fallback_body_shape`, `compile_internal_function_shape`, `compile_internal_fn_bodies_shape`, `supported_function_body_shape`, `package_external_fn_shape_ok`, `package_internal_fn_shape_ok`, `package_fallback_fn_shape_ok`, `compiler_label_prefix`, `jump_label_ok_names`, `MEM_fn_insts_blocks_iff`, `get_successors_jump_label_ok`, `bb_succs_jump_label_ok`, `lowered_fn_ok`, `internal_fns_ok`, `lowered_unit_source_ok`, `package_internal_blocks_segments`, `internal_name_not_entry_label`, `run_lowering_source_unit_ok`, `build_selectors_fn_labels`, `supported_internal_descriptors_ok`.
- Put every helper lemma in `loweringShapePropsScript.sml` directly above `compile_generate_runtime_shape` (other provers are adding helpers above their own targets in the same file). No new theory files.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target script | `lowering/proofs/loweringShapePropsScript.sml` | side-condition definitions, generator lemmas, composition |
| Framework | `lowering/proofs/loweringShapeDefsScript.sml` | `shape_step` and its rules: `shape_step_bind`, `_ignore_bind`, `_return`, `_conseq`, `_frame`, `_comp_get`, `_fresh_var(s)`, `_fresh_id`, `_fresh_label`, `_new_block`, `_emit`, `_emit_op`, `_emit_inst`, `_emit_void`, `_emit_multi_op`, `_emit_op_gas`, `_emit_op_call`, `_emit_op_retpc`, `_emit_inst_ret`; stability lemmas `*_mono`, `shape_stable_*` |
| Shape predicates | `venom/compiler/unitShapeDefsScript.sml` | `o1_source_unit_ok`, `raw_opcode_ok`, `inst_shape_ok`, `opaque_use_ok`, `is_param_opcode` |
| Compile monad | `lowering/defs/compileEnvScript.sml`, `lowering/defs/emitHelperScript.sml` | `compile_state`, `comp_bind`, `fresh_var`, `fresh_label`, `new_block`, `emit_op`, `not_fresh_at`, `compile_env` |
| Lowering | `lowering/defs/exprLoweringScript.sml`, `lowering/defs/stmtLoweringScript.sml`, `lowering/defs/contextScript.sml`, `lowering/defs/abiEncoderScript.sml`, `lowering/defs/builtin*Script.sml`, `lowering/defs/moduleLoweringScript.sml`, `lowering/defs/vyperCompilerScript.sml`, `lowering/defs/compileVyperScript.sml` | the generators; `compile_expr_ind`, `compile_stmt_ind`, `compile_expr_raw_def` |
| Existing lowering props | `lowering/emitHelperPropsScript.sml`, `lowering/exprLoweringPropsScript.sml`, `lowering/stmtLoweringPropsScript.sml`, `lowering/moduleLoweringPropsScript.sml`, `lowering/contextPropsScript.sml`, `lowering/abiEncoderPropsScript.sml`, `lowering/builtinPropsScript.sml`, `lowering/proofs/compilePhasesPropsScript.sml`, `lowering/proofs/freshLabelStringPropsScript.sml` | equations, `cs_extends` and label facts about the generators (`compileVyperScript.sml` in `lowering/defs` also has the `internal_fn_descriptors_*` lemmas) |
| Supported subset | `lowering/supported/` (`supportedProgramScript.sml`, `supportedExprsScript.sml`, `supportedExprFormsScript.sml`, `supportedStmtTraverseScript.sml`, `supportedExprTraverseScript.sml`, `supportedNamesScript.sml` and their `*PropsScript.sml`) | `supported_program`, the `supported_*_exists` traversals and their lemmas |
| HOL sources | `.holbuild/src/` after `holbuild context`; HOL toolchain under `$HOLDIR` | library theorems |

## Notes

The cheated lemmas were checked by reading the lowering against their statements before this task; no counterexample is known. A first review found and fixed one false case (builtins with fewer arguments than their dispatcher reads compile `HD []`; `expr_shape_root` now excludes them).
