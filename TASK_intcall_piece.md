# TASK: the internal-call case of the body simulation (s1-calls piece intcall)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/ (file lowering/bodySimCallIntcallScript.sml)

## Theorem Statement (FROZEN)

In lowering/bodySimCallIntcallScript.sml:

```sml
Theorem intcall_body_expr_ok:
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

The judgments are in lowering/bodySimScript.sml: `body_inv`, `body_expr_ok`, `body_stmts_ok`, `body_exprs_ok`, `body_results_ok`, `frame_ret_ok`, `locals_alloc_ok`, `stmt_exprs_ok`, `ce_locals_declared`. `expr_body_pre` and `expr_sim_inv` are in lowering/exprSimHypsDefsScript.sml; `expr_sim`, `expr_vv_sim`, `expr_exit` in lowering/exprSimDefsScript.sml; `stmt_frag`, `stmt_framed_frag`, `stmt_state_rel` in lowering/stmtSimDefsScript.sml; `ret_pc_ok`, `return_buf_frame` in lowering/loweringPostsScript.sml; `gas_outcome`, `gas_admissible` in the gas theories (lowering/fragGas*Script.sml, lowering/gasSummary*Script.sml).

**Do not modify this statement or any of these definitions.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `timeout 5400 holbuild -j4 build bodySimCallIntcallTheory bodySimCallCasesTheory exprSimCallsTheory` passes with no CHEAT in `intcall_body_expr_ok`, in any helper you add, or in any theory you add or port, and no FAILs, at the default 2.5 s tactic timeout.
2. The proof may cite theorems of shared theories that this worktree admits locally (the commit "LOCAL OVERLAY" replaces their proofs with `cheat`; they are proved on other branches). Add no new `cheat` of your own anywhere.
3. Helpers in their most general form, no duplicates of existing lemmas (search before adding; a `[local]` lemma of a shared theory you need is not copied, report it instead). Large developments go in leaf theory files under lowering/ that only `bodySimCallIntcall` (directly or through other such leaf files) lists in `Ancestors`.
4. No `TRY`/`ORELSE`/`FIRST` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).
5. Commit only the .sml files you changed or added under lowering/ (never the overlay's files, `.alan/`, `PLAN_*`, `STATE_*`, `LEARNINGS_*`, `LOG_*`, `DOSSIER_*`, tool outputs). Commit messages end with the trailers
   `Bot: opus (Claude Opus 5.5)` and
   `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

**If the theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement.

## Build

```
timeout 5400 holbuild -j4 build bodySimCallIntcallTheory bodySimCallCasesTheory exprSimCallsTheory
```
(run from the project root, the directory containing holproject.toml; while iterating, build the theory you are working on)

## Background

The body simulation is one induction over the source evaluator, one case per evaluator clause; `bodySimCallCases` assembles the call cases from leaf pieces, and this is the internal-call piece: `Call _ (IntCall (src_id_opt,fn)) es _`. The IHs give the arguments' judgments, the defaults' and the callee body's `body_stmts_ok` at `cxf`, the context after `push_function`. The lowering (`compile_call` in lowering/defs/exprLoweringScript.sml) stages the arguments, INVOKEs the callee's label, and reads the results back; the callee's code was generated by `compile_internal_function` (lowering/defs/moduleLoweringScript.sml), packaged by `package_internal_fn`, inside `lower_vyper_runtime_unit` or, when `cx.in_deploy`, `lower_vyper_deploy_unit` (lowering/defs/compileVyperScript.sml), whose context is `ctx` by `body_inv`.

The judgments are counted: `expr_sim`/`stmt_frag` state a `gas_outcome` of the source computation over every gas-reading sequence, admissible by `gas_admissible`, not a single `eval_stmt ... = (res, es')` run.

Facts about the setting (checked against the definitions, not proofs):
- `body_inv` covers both units: `cx.in_deploy` selects the deploy unit, and `cenv.ce_is_ctor <=> cx.in_deploy`. In deploy, `body_inv` also has that tops declares a constructor (`IS_SOME (SND (SND (SND (classify_functions tops))))`), so `lower_vyper_deploy_unit` packages every internal function with `is_ctor = T`. `expr_body_pre` has, for every internal call `c` of the expression, `IS_SOME (supported_function_decl tops c Internal)`, so `lookup_callable_function cx.in_deploy fn ts` takes its `Internal` branch in both modes (its `Deploy` fallback, a synthetic empty constructor for undeclared names, never applies).
- `supported_program` (lowering/supported/) gives every function `~nr` and `NULL defaults`, and an internal function's body makes no internal calls (`expr_internal_call_root`). The source type checker rejects an internal `@raw_return` (`function_header_ok` in semantics/type/vyperTypeContractScript.sml).
- `fn_allocs_ok_body` (lowering/allocLimitsPropsScript.sml) and `lower_vyper_runtime_unit_allocs_ok` (compileVyper) give, for the callee: its parameters' and return type's sizes below 2 ** 64, `alloc_limits_stmts` of its body and `alloc_limits_expr` of every expression in it.
- `compile_internal_function` compiles a `NoneT` callee's body at `BoolT` (`case ret_type of SOME t => t | NONE => BaseT BoolT`), while the typing has `NoneT`.
- `call_evaluation_safe_push_body` (semantics/prop/vyperTypeCallStackSoundnessScript.sml) moves `call_evaluation_safe` into the callee body; `functions_well_typed` (semantics/prop/vyperTypeInvariantsScript.sml), part of `expr_sim_inv`, types the callee body. `fn_sigs_consistent` (same file) gives the callee's signature from `env.fn_sigs`.
- The comment above `intcall_body_expr_ok` maps the call's steps to existing lemmas, and says what is left (the push transfer to the callee's entry).

Harvest: lowering/bodyIntCall*Script.sml (47 leaf theories) come from an earlier attempt at this case on an older base (before the counted-GAS join and before `body_inv` covered the deploy unit; that base had `~cx.in_deploy` in `body_inv`). They are yours: port, restate, split, replace or delete them and their theorems as the proof needs; nothing outside these files imports them. As copied, these build here: bodyIntCallArgs, ContextLabels, EntryEnv, HeadroomProbe, LabelFrame, LabelReservations, Labels, MaterialLabels, Prefix, Return, StorageFrame, TypeEval, TypingTransfer. bodyIntCallSourceFrame fails (`supported_builtin_no_gas_or_len`: `msg.gas` is supported now, and evaluating it consumes `gas_obs`, so "only outcomes change" frames need `gas_obs` too); the rest were not reached. ExprObserver, ObserverFrame, PostObservation and SemanticFrame were added last and are unbuilt here. bodyIntCallCode and bodyIntCallCodeCopy use lemmas of intCallLookup (`lookup_function_distinct_mem`, `run_lowering_descriptors_distinct`) and exprSimStorageCopy (`storage_copy_bind_eq`, `storage_copy_header_layout`, `storage_copy_init_layout`, `storage_copy_prefix_freshness`); these are exported on this base.
bodyIntCallArgLifetime used `compile_expr_operand_not_label`, which the old base added to exprReasonOperand and this base lacks; prove it in a leaf (from `compile_expr_reason_uniform`).

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, `rename1` rather than generated names.
- Don't change any existing theorem statement or definition outside the bodyIntCall* leaf files. Add new definitions only if unavoidable, and say so in the commit message.
- Never edit shared theories (anything not lowering/bodyIntCall*Script.sml or lowering/bodySimCallIntcallScript.sml), and never the LOCAL OVERLAY changes.
- New theories under lowering/ are reached through `Ancestors`; leave `holproject.toml` alone.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| target | lowering/bodySimCallIntcallScript.sml | intcall_body_expr_ok and its proof-plan comment |
| consumer | lowering/bodySimCallCasesScript.sml | how the piece is used |
| judgments | lowering/bodySimScript.sml | body_inv, body_*_ok, frame_ret_ok |
| expr judgments | lowering/exprSimDefsScript.sml, lowering/exprSimPropsScript.sml, lowering/exprSimHypsDefsScript.sml, lowering/exprSimHypsScript.sml | expr_sim, expr_vv_sim, expr_body_pre, expr_sim_inv |
| stmt judgments | lowering/stmtSimDefsScript.sml, lowering/stmtSimPropsScript.sml, lowering/loweringPostsScript.sml | stmt_frag, stmt_state_rel, ret_pc_ok |
| counted gas | lowering/gasIntCallArgsScript.sml, lowering/gasIntCallBodyScript.sml, lowering/gasSummary*Script.sml, lowering/gasExemptCertScript.sml, lowering/fragGas*Script.sml | counted outcomes, internal-call argument and body gas transport |
| entry | lowering/bodySimEntryScript.sml | internal_entry_declared, ce_locals_declared_params, body_inv_build_internal_env |
| the call's steps | lowering/intCallStepScript.sml, intCallLookupScript.sml, intCallArgsScript.sml, intCallCalleeScript.sml, intCallReturnScript.sml, intCallReturnMemScript.sml, intCallFrameScript.sml, intCallResultScript.sml | compile_call_intcall_shape/label, lower_vyper_runtime_unit_internal_lookup, stage_mem_arg_frag, compile_internal_prologue_entry, frag_exec_invoke_intret, eval_expr_intcall_return, invoke_intret_state_rel, store_multi_results_frag, compile_internal_return_memory_frag, intret_mem_q |
| returns | lowering/stmtSimReturn*Script.sml | intret_q, compile_return_word_int_frag, compile_return_tuple_int_frag |
| other proved expr cases | lowering/bodySimExprCasesScript.sml, lowering/exprSimCall*Script.sml | how a body case discharges expr_sim/expr_vv_sim in the counted setting |
| alloc limits | lowering/defs/allocLimitsScript.sml, lowering/allocLimitsPropsScript.sml | fn_allocs_ok, fn_allocs_ok_body |
| the lowering | lowering/defs/exprLoweringScript.sml, moduleLoweringScript.sml, compileVyperScript.sml | compile_call, compile_internal_function, package_internal_fn, lower_vyper_runtime_unit, lower_vyper_deploy_unit, build_compile_env |
| source semantics | semantics/vyperInterpreterScript.sml | eval_expr IntCall, push_function, bind_arguments, lookup_callable_function |
| type soundness | semantics/prop/ | functions_well_typed, fn_sigs_consistent, call_evaluation_safe_push_body |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | INVOKE, setup_callee, exec_gas |
| harvest | lowering/bodyIntCall*Script.sml | see Background |
| expression-family storage frames (late harvest) | lowering/bodyIntCallExprFrameScript.sml, bodyIntCallForceTransferScript.sml, bodyIntCallAggregateCopyScript.sml, bodyIntCallMappingFrameScript.sml, bodyIntCallSemanticFrameScript.sml (updated), bodyIntCallExprObserverScript.sml (updated), bodyIntCallExprBodyLabelsScript.sml | Per-family storage/transient frame producers for compile_expr (name, literal, unwrap, not, abs, mapping subscript, aggregate copy, ...), from the earlier internal-call run's final state, written against the old base (non-counted frag_exec, old body_inv). Not yet built on this base: port what the universal expression-family producer needs, drop the rest. |
