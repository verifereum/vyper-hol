# TASK: S3 entry seam: argument registration reaches the body with the ghost

## Meta
Status: planned
Priority: P1
Created: 2026-11-08
Location: lowering/entryPtrSeamRegisterScript.sml

## Theorem Statement (FROZEN)

1 theorem, currently `cheat` in `lowering/entryPtrSeamRegisterScript.sml`. Prove it. Copy of the statement as it stands in the source:

```sml
Theorem register_positional_args_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 efn elbl lbl cenv0
   pos_args min_cds is_payable nkey ut' iv rt st cenv sa s1 G1 tn1.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
    fn_has_code st sa efn /\ fn_inst_ids_distinct efn /\
    vars_pc_only
      (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                  vs_inst_idx := 0 |>) s1 /\
    fresh_vars_wrt st s1 /\ ~s1.vs_halted /\
    s1.vs_current_bb = st.cs_current_bb /\
    s1.vs_inst_idx = LENGTH st.cs_current_insts /\
    tn1.t_mem = {} /\ tn1.t_stor = {} /\ tn1.t_trans = {} /\
    tn1.t_imm = {} ==>
    ?s0 G0 tn0.
      stmt_state_rel unit.cu_context efn cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
      ghost_inv NONE cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) es0
        G0 tn0 s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      !D. (!fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G0 tn0 s0) ==>
          !fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G1 tn1 s1
```

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

## Completion Criteria

1. `holbuild -j4 build entryPtrSeamRegisterTheory` passes with `register_positional_args_ptr` proved: no `cheat` in `lowering/entryPtrSeamRegisterScript.sml` nor in any theory this run adds, and no FAILs.
2. Nothing in `lowering/loweringPtrCorrectScript.sml` or the other `lowering/entryPtrSeam*Script.sml` files changes.
3. No duplicate or near-duplicate lemmas; helpers in their most general form.

**If the theorem is false as stated:**
- Produce a counterexample.
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build entryPtrSeamRegisterTheory
```

Run from the project root (the directory holding `holproject.toml` and this file).

## Background

S3 says the lowered Vyper unit's raw Venom run satisfies the pointer discipline and keeps taint within the source call's dead bytes. Its entry theorem `external_entry_reaches_body_ptr` (in `lowering/loweringPtrCorrectScript.sml`) is now proved from five seams, each its own theory with one `cheat`ed theorem: `entryPtrSeamDead` (the body's dead bytes are the call's), `entryPtrSeamPrefix` (selector dispatch and passing entry checks), `entryPtrSeamRegister` (argument registration reaches the body's start with the S1 relation and the ghost), `entryPtrSeamDecoder` (the pointer-safe calldata decoder contract for every coherent type) and `entryPtrSeamBulk` (its bulk-copy dynamic-array case). This task proves one of them.

A pointer-safe run (`ptr_safe_run`/`ptr_safe_blocks`, `venom/compiler/ptrSafeRunScript.sml`) checks each executed instruction against `ptr_inst_ok` while threading a ghost: provenance `G` (pointer variable -> base, size) and taint `tn` (tainted variables and memory, storage, transient bytes). The judgments in `lowering/bodyPtrDefsScript.sml` (`ptr_covers`, `ghost_inv`, `mem_agree_outside`, `cx_dead`, ...) are the pointer twins of S1's. The selector dispatch and the entry checks touch no memory; the argument decode writes only the parameters' buffers (ALLOCAs whose provenance the ghost records), from calldata, so untainted.

This seam: From the state the entry checks leave (as `entryPtrSeamPrefix` provides it), `compile_register_positional_args` allocates a buffer per parameter and decodes the argument from calldata into it. The seam says the run reaches the guarded body's start `s0` with the S1 relation (`stmt_state_rel`, as S1's admitted `external_entry_reaches_body` states it, here at the state actually reached) and a ghost in `ghost_inv NONE`, and that safety from `s0` gives safety from the registration's start. Only `abi_decoder_coherent` types' decoder contract is assumed (the sibling seam); establishing its inputs from `valid_vyper_call`'s calldata encoding, the word path, the per-parameter frames and the induction over the parameters are this seam's work.

## Domain Constraints

- Build with holbuild only (no Holmake). The tactic timeout is the project default, 2.5 s per step; don't raise it, and pass no timeout flags.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Don't edit proven statements in other theories, and don't change any definition (in particular nothing in `lowering/defs/`, `venom/`, `lowering/bodyPtrDefsScript.sml`, `lowering/bodyMemoryDefs*`). Don't add axioms or new `cheat`s. No `let` in theorem statements.
- Leave `lowering/loweringPtrCorrectScript.sml` alone: its theorems (`external_entry_reaches_body_ptr`, `external_entry_value_revert_ptr`, `external_frame_ret_ok_ptr`, `body_stmts_sim_ptr` and the rest) are not this task's; don't prove, restate or edit them. Don't edit the other `entryPtrSeam*Script.sml` files either.
- New helper lemmas go in new theories under `lowering/` named for what they prove, or in this seam's own theory file. A new theory must be an ancestor of this seam's theory so its build reaches it. You may use and extend the lane's proved helper theories (`lowering/*PtrScript.sml` and their ancestors); a restated variant of one of them gets a new name, its original stays.
- The named admissions already in the tree may be used as given: S1's in `lowering/loweringRuntimeCorrectScript.sml`, and the sibling seams `calldata_scratch_decoder_ptr` (`lowering/entryPtrSeamDecoderScript.sml`) and `calldata_scratch_array_copy_decoder_ptr` (`lowering/entryPtrSeamBulkScript.sml`), both ancestors. Don't prove, restate or weaken them.
- Commit only proof sources (no task/state/plan/log files). Commit trailer: `Bot: opus (Claude Opus 5.5)`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| this seam | lowering/entryPtrSeamRegisterScript.sml | the frozen statement, with hints as comments above it |
| the composer | lowering/loweringPtrCorrectScript.sml | how `external_entry_reaches_body_ptr` consumes the seams (read only) |
| ptr judgments | lowering/bodyPtrDefsScript.sml | cx_dead, mem_agree_outside, ptr_covers, return_buf_ptr, stor_taint_ok, ghost_inv |
| pointer-safe runs | venom/compiler/ptrSafeRunScript.sml | ptr_inst_ok, ptr_safe_run/blocks, ghost_run, fuel lemmas |
| pointer discipline | venom/compiler/ptrDisciplineScript.sml | access_ok, taint_ok, step_prov/step_taint, entry_taint, allocas_from, ctx_has_dalloca |
| decoder contract | lowering/entryPtrSeamDecoderScript.sml | calldata_scratch_decoder_ptr (admitted sibling seam) |
| ordinary registration | lowering/entryStateRelScript.sml, lowering/entryArgPtrsScript.sml, lowering/entryDecodePlanPropsScript.sml, lowering/entryDecodePropsScript.sml, lowering/entryLocalsScript.sml | the static-only S1 registration (external_body_entry_state_rel), head offsets, word decode |
| memory-sourced caller | lowering/abiBuiltinValidCallerScript.sml and its ancestors | decoder inputs established for the abi_decode builtin |
| lowering definitions | lowering/defs/moduleLoweringScript.sml, lowering/defs/contextScript.sml | compile_register_positional_args, compile_decode_args, compile_alloc_buffer |
| S1 relation | lowering/exprLoweringPropsScript.sml | stmt_state_rel |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml, venom/defs/venomStateScript.sml | step_inst, run_from, state |

## Notes

- Hints for this seam are SML comments above its statement; they are not binding.
- Build with `-j4` at most; never `holbuild run`/`repl`.
