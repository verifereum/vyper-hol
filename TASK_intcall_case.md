# TASK: the internal call case of the body simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-01
Location: lowering/ (file lowering/bodySimExprCasesScript.sml)

## Theorem Statement (FROZEN)

In lowering/bodySimExprCasesScript.sml:

```sml
Theorem body_intcall_case:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8' s'11' rtv
         t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7' prev
         t'5' s'8' x'' t'6'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') /\
       eval_expr_results cx es s'6' = (INL results,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3'.
       type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
       lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" s'3' = (INL ts,t') /\
       lift_option_type (lookup_callable_function cx.in_deploy fn ts)
         "IntCall lookup_function" s'4' = (INL tup,t'') /\ mut = FST tup /\
       stup = SND tup /\ (nr <=> FST stup) /\ stup2 = SND stup /\
       args = FST stup2 /\ sstup = SND stup2 /\ dflts = FST sstup /\
       sstup2 = SND sstup /\ ret = FST sstup2 /\ body' = SND sstup2 /\
       type_check
         (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
         "IntCall args length" s'5' = (INL x',t'3') ==>
       body_results_ok cx es) ==>
    body_expr_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
```

The judgments are in lowering/bodySimScript.sml: `body_inv`, `body_expr_ok`, `body_stmts_ok`, `body_exprs_ok`, `body_results_ok`, `frame_ret_ok`, `locals_alloc_ok`, `stmt_exprs_ok`, `ce_locals_declared`. `expr_body_pre` and `expr_sim_inv` are in lowering/exprSimHypsScript.sml; `expr_sim`, `expr_vv_sim` in lowering/exprSimScript.sml; `stmt_frag`, `ret_pc_ok`, `stmt_state_rel` in lowering/stmtSimScript.sml.

**Do not modify this statement or any of these definitions.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `timeout 5400 holbuild --max-heap 8000 -j4 build bodySimMainTheory` passes, with no CHEAT in `body_intcall_case`, in any helper you add, or in any theory you add, and no FAILs, at the default 2.5 s tactic timeout. The other cheated cases in bodySimExprCases/bodySimStmtCases (body_extcall_case, body_raw_call_case, the builtin residuals, ...) are out of scope and stay as they are.
2. One exception is allowed: a `Return` whose value widens to the function's return type through `compile_store_memory_typed` with differing aggregate layouts (DynArray or tuple-of-bytestring widening; the comment on `supported_return_layout` says these still need an independent repair, #560). If that case of `frame_ret_ok` is false or blocked, isolate it in ONE helper theorem stating exactly that case, prove it with `cheat` and a comment beginning `(* RESIDUAL (#560):` that says why, and report it. Nothing else may be cheated.
3. Helpers in their most general form, no duplicates of existing lemmas. Put large developments (callee entry transfer, code locality of the generated runtime, return shapes) in new theory files under lowering/ that bodySimExprCases lists in `Ancestors`; small glue may go in bodySimExprCasesScript.sml before the theorem.
4. No `TRY`/`ORELSE`/`FIRST` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).
5. Commit only the .sml files you changed or added (never `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*`, tool outputs). Commit messages end with the trailers
   `Bot: opus (Claude Opus 5.5)` and
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

**If the theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement.

## Build

```
timeout 5400 holbuild --max-heap 8000 -j4 build bodySimMainTheory
```
(run from the project root, the directory containing holproject.toml; while iterating, build the theory you are working on, e.g. `bodySimExprCasesTheory`)

## Background

The body simulation (lowering/bodySimMainScript.sml, `body_sim_mutual`) is one induction over the source evaluator, one case per evaluator clause. This is the case for an internal call `Call _ (IntCall (src_id_opt,fn)) es _`: the IHs give the arguments' judgments, the (empty, see below) defaults' and the callee body's `body_stmts_ok` at `cxf`, the context after `push_function`. The lowering (`compile_call` in lowering/defs/exprLoweringScript.sml) stages the arguments, INVOKEs the callee's label, and reads the results back; the callee's code was generated by `compile_internal_function` (lowering/defs/moduleLoweringScript.sml) inside `lower_vyper_runtime_unit` (lowering/defs/compileVyperScript.sml), whose context is `ctx` by `body_inv`.

Facts about the setting (checked against the definitions, not proofs):
- `supported_program` (lowering/supported/supportedProgramScript.sml, supportedDeclsScript.sml) gives every function `~nr`, `~rr` and `NULL defaults`, and an internal function's body makes no internal calls (`expr_internal_call_root`).
- `body_inv` has `~cx.in_deploy`, so `lookup_callable_function F fn ts` finds a runtime function of `tops`.
- `lower_vyper_runtime_unit_allocs_ok` (compileVyper) and `fn_allocs_ok_body` (lowering/allocLimitsPropsScript.sml) give, for the callee: its parameters' and return type's sizes below 2 ** 64, `alloc_limits_stmts` of its body and `alloc_limits_expr` of every expression in it.
- `ret_pc_ok` (stmtSim) binds the return PC and, for a memory return, the return-buffer variable with `w2n w + sz + 64 < dimword (:256)`; `stmt_frag` assumes it of its start state.
- `compile_internal_function` compiles a `NoneT` callee's body at `BoolT` (`case ret_type of SOME t => t | NONE => BaseT BoolT`), while the typing has `NoneT`.
- `call_evaluation_safe_push_body` (semantics/prop/vyperTypeCallStackSoundnessScript.sml) moves `call_evaluation_safe` into the callee body; `functions_well_typed` (semantics/prop/vyperTypeInvariantsScript.sml), part of `expr_sim_inv`, types the callee body.
- `lower_vyper_runtime_unit_internal_lookup` (lowering/intCallLookupScript.sml) only gives the callee's function in ctx existentially; nothing yet ties its blocks to the compile states of `stmts_env` for the body.
- `alloca_room_callee` (lowering/exprLoweringPropsScript.sml) gives the callee's alloca room from the caller's.
- The GAP comment above `body_intcall_case` maps the call's steps to existing lemmas.

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, `rename1` rather than generated names.
- Don't change any existing theorem statement or definition. Add new definitions only if unavoidable, and say so in the commit message.
- New theories under lowering/ are reached through `Ancestors`; leave `holproject.toml` alone.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| target | lowering/bodySimExprCasesScript.sml | body_intcall_case and its GAP comment |
| judgments | lowering/bodySimScript.sml | body_inv, body_*_ok, frame_ret_ok |
| entry | lowering/bodySimEntryScript.sml | internal_entry_declared, ce_locals_declared_params |
| the call's steps | lowering/intCallStepScript.sml, intCallLookupScript.sml, intCallArgsScript.sml, intCallCalleeScript.sml, intCallReturnScript.sml, intCallReturnMemScript.sml, intCallFrameScript.sml, intCallResultScript.sml | compile_call_intcall_shape/label, lower_vyper_runtime_unit_internal_lookup, stage_mem_arg_frag, compile_internal_prologue_entry, frag_exec_invoke_intret, eval_expr_intcall_return, invoke_intret_state_rel, callee_writes_above, store_multi_results_frag, compile_internal_return_memory_frag, intret_mem_q |
| returns | lowering/stmtSimReturnScript.sml | intret_q, compile_return_word_int_frag, compile_return_tuple_int_frag |
| alloc limits | lowering/defs/allocLimitsScript.sml, lowering/allocLimitsPropsScript.sml, lowering/defs/compileVyperScript.sml | fn_allocs_ok, fn_allocs_ok_body, lower_vyper_runtime_unit_allocs_ok |
| byte widths | lowering/entryStateRelScript.sml | evaluate_type_int_byte_widths (l. ~590) |
| the lowering | lowering/defs/exprLoweringScript.sml, moduleLoweringScript.sml, compileVyperScript.sml | compile_call, compile_internal_function, compile_generate_runtime, package_internal_fn, build_compile_env |
| source semantics | semantics/vyperInterpreterScript.sml | eval_expr IntCall, push_function, bind_arguments, lookup_callable_function |
| type soundness | semantics/prop/ | functions_well_typed, call_evaluation_safe_push_body |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | INVOKE, setup_callee |
