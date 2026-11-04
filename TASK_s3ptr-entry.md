# TASK: S3 pointer-safe run: the entry and the frame returns

## Meta
Status: planned
Priority: P1
Created: 2026-11-03
Location: lowering/loweringPtrCorrectScript.sml

## Theorem Statement (FROZEN)

3 theorem(s), each currently `cheat` in `lowering/loweringPtrCorrectScript.sml`. Prove all of them. Copy of each statement as it stands in the source:

```sml
Theorem external_entry_value_revert_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env e st efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. ptr_safe_blocks
             (external_call_dead tx
                (call_external (SOME vs.vs_outcomes) [] am tx))
             0 fuel unit.cu_context efn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)

Theorem external_entry_reaches_body_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops F (assign_nkeys tops 0)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      stmt_state_rel unit.cu_context func cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ghost_inv NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0
        G0 tn0 s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      cenv.ce_return_buf = NONE /\
      ((!fuel. ptr_safe_run
                 (cx_dead
                    (initial_evaluation_context am.sources am.layouts tx
                       NONE))
                 0 fuel unit.cu_context func [] G0 tn0 s0) ==>
       !fuel. ptr_safe_blocks
                (external_call_dead tx
                   (call_external (SOME vs.vs_outcomes) [] am tx))
                0 fuel unit.cu_context efn [] FEMPTY entry_taint
                (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                            vs_inst_idx := 0 |>))

Theorem external_frame_ret_ok_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
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
    frame_ret_ok_ptr NONE unit.cu_context [] func
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (\v es gt r. T) cenv ret
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build loweringPtrCorrectTheory` passes with each theorem above proved (no `cheat` in their proofs, nor in any helper you add) and no FAILs.
2. The other `cheat`s in `lowering/loweringPtrCorrectScript.sml` (`body_stmts_sim_ptr`, `compile_guarded_body_end_ptr_safe`, `lower_vyper_runtime_unit_run_ptr_safe_composed`) stay as they are; other runs prove them in other branches.
3. No duplicate or near-duplicate lemmas; helpers in their most general form.

**If a theorem is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build loweringPtrCorrectTheory
```

Run from the project root (the directory holding `holproject.toml` and this file).

## Background

S3 says the lowered Vyper unit's raw Venom run satisfies the pointer discipline (`ptr_discipline 0`) and keeps taint within the source call's dead bytes (`taint_within (external_call_dead ...)`). `lower_vyper_runtime_unit_ptr_taint` (in `lowering/loweringMemCorrectScript.sml`) is proved from `ptr_safe_ptr_discipline` and `lower_vyper_runtime_unit_run_ptr_safe_composed` (in `lowering/loweringPtrCorrectScript.sml`), which rests on this task's theorems and `body_stmts_sim_ptr`. A pointer-safe run (`ptr_safe_run`/`ptr_safe_blocks`, `venom/compiler/ptrSafeRunScript.sml`) checks each executed instruction against `ptr_inst_ok` while threading a ghost: provenance `G` (pointer variable -> base, size) and taint `tn` (tainted variables and memory, storage, transient bytes). `cx_dead cx` gives the call's dead storage bytes.

The judgments in `lowering/bodyPtrDefsScript.sml` are the pointer twins of S1's (`frag_exec`, `expr_sim`, `stmt_frag`, `frame_ret_ok` in `lowering/fragExecScript.sml`, `lowering/stmtSimScript.sml`, `lowering/bodySimScript.sml`): each adds the ghost to the state and the pointer-safety of the run. The composition is shaped like S1's (`lower_vyper_runtime_unit_correct` in `lowering/loweringRuntimeCorrectScript.sml`) and like the memory-safe twin (`lowering/loweringMemCorrectScript.sml`).

These are the pointer twins of S1's `external_entry_value_revert`, `external_entry_reaches_body` and `external_frame_ret_ok` (`lowering/loweringRuntimeCorrectScript.sml`; S1 admits the first). The selector dispatch and the entry checks touch no memory; the argument decode writes only the parameters' buffers (ALLOCAs whose provenance the ghost records), from calldata, so untainted; the return sequences encode into a fresh buffer and RETURN or REVERT only bytes they wrote. At a halt, `ptr_inst_ok` asks the storage and transient taint to lie inside the call's dead bytes and the returned bytes to be untainted.

## Domain Constraints

- Build with holbuild only (no Holmake). The tactic timeout is the project default, 2.5 s per step; don't raise it, and pass no timeout flags.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Don't edit proven statements in other theories, and don't change any definition (in particular nothing in `lowering/defs/`, `venom/`, `lowering/bodyPtrDefsScript.sml`, `lowering/bodyMemoryDefs*`). Don't add axioms or new `cheat`s. No `let` in theorem statements.
- New helper lemmas go in new theories under `lowering/` (name them for what they prove, e.g. `lowering/entryHaltPtrScript.sml`), or in `lowering/loweringPtrCorrectScript.sml`. A new theory must be an ancestor of `loweringPtrCorrect` so the build reaches it.
- The other named admissions in `lowering/loweringPtrCorrectScript.sml`, and S1's admissions in `lowering/loweringRuntimeCorrectScript.sml`, may be used as given; don't prove, restate or weaken them unless this task lists them.
- Commit only proof sources (no task/state/plan/log files). Commit trailer: `Bot: opus (Claude Opus 5.5)`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| the frozen statements and the other admissions | lowering/loweringPtrCorrectScript.sml | this task's theorems |
| ptr judgments | lowering/bodyPtrDefsScript.sml | cx_dead, mem_agree_outside, ptr_covers, return_buf_ptr, stor_taint_ok, ghost_inv, ghost_kept, ptr_mem_ok, ptr_val_ok, ptr_vv_ok, frag_exec_ptr, expr_sim_ptr, expr_vv_sim_ptr, stmt_exit_ptr, stmt_frag_ptr, frame_ret_ok_ptr |
| pointer-safe runs | venom/compiler/ptrSafeRunScript.sml | ptr_inst_ok, ptr_safe_run/blocks, ghost_run, fuel lemmas, ptr_safe_ptr_discipline bridge |
| pointer discipline | venom/compiler/ptrDisciplineScript.sml | access_ok, taint_ok, out_taint, step_prov/step_taint, entry_taint, external_call_dead, fn_ptr_ok, ctx_has_dalloca |
| S1 composition and judgments (the template) | lowering/loweringRuntimeCorrectScript.sml, lowering/bodySimScript.sml, lowering/bodySimMainScript.sml, lowering/stmtSimScript.sml, lowering/exprSimScript.sml, lowering/fragExecScript.sml | the non-pointer twins: lower_vyper_runtime_unit_correct, external_entry_*, external_frame_ret_ok, body_stmts_sim, stmt_frag, frame_ret_ok, frag_exec |
| memory-safe twin | lowering/{bodyMemoryDefs,entryHaltMem,loweringMemCorrect,fragExecMem}Script.sml | the same composition for mem_safe_run; entryHaltMem is fully proved |
| helper theories from an earlier attempt | lowering/*PtrScript.sml (fragExecPtr, entryHaltPtr, typedCopy*Ptr, batchCopyRobustPtr, normalizationAllocPtr, robustCopyTransportPtr, ...) and lowering/typedCopy*Lib.sml | proved on an older base; already ancestors of loweringPtrCorrect. Port them to this base where they no longer build, reuse what holds, delete what isn't needed |
| halt and entry pieces | lowering/loweringHaltScript.sml, lowering/entryArgPtrsScript.sml, lowering/entryDecodePlanPropsScript.sml, lowering/abiDecodeStaticPropsScript.sml | return sequences and argument decode runs |
| lowering definitions | lowering/defs/moduleLoweringScript.sml, lowering/defs/stmtLoweringScript.sml, lowering/defs/exprLoweringScript.sml, lowering/defs/compileEnvScript.sml | compile_guarded_body, compile_register_positional_args, ... |
| source exemption | lowering/e2eDefsScript.sml | source_exempt, unspecified_behaviour_exempt (covers RuntimeError "convert empty bytes to signed") |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml, venom/defs/venomStateScript.sml | step_inst, run_from, state |

## Notes

- `external_entry_reaches_body_ptr` gives the body's start ghost `G0 tn0` existentially; choose it so that `ghost_inv NONE` holds there (every live PtrVar local covered and robust).
- `entryHaltMem` in the memory twin is the closest worked example of these leaves.
- `external_entry_reaches_body_ptr` and `external_frame_ret_ok_ptr` pass the selected function's raw-return flag (`lookup_raw_return_or_F`) to `package_external_fn`, as their memory twins and S1's `external_body_frame` do.
