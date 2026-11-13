(*
 * The pointer twin of bodySimMain's induction: the cases for the internal call.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_intcall_case_ptr
 *)
Theory bodyPtrIntCallCase
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  bodyPtrIntCallFrameRet bodyPtrIntCallArrayHeader bodyPtrIntCallConcreteFields
  bodyPtrIntCallEntryContracts bodyPtrIntCallMargin
  bodyPtrIntCallRunConfinement bodyPtrIntCallStaticArrayCopy
  bodyPtrIntCallWordStore bodyPtrIntCallPrologue bodyPtrIntCallScratch
  bodyPtrIntCallArgumentLayout
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* Pointer seam interface audit (C1.1).
 *
 * All seam parameters below are universally quantified, including the
 * caller's d, PG, G0, tn0, es0, s0, sa, sb and compiled value vv.  The
 * caller precondition is exactly expr_vv_sim_ptr_def's antecedent plus
 * body_inv, expr_body_pre, source selection, and the argument pointer IH.
 * Do not replace this by the S1 seam antecedent: that loses the ghost.
 *
 * STAGING: for each continuation Q R, prove gas_outcome_ptr for the
 * whole call provided the continuation proves it for intcall_rest at
 * every reached (prev,penv,rtv,es1,t,G,tn).  In addition to intcall_entry,
 * its entry must carry ghost_inv d cenv cx (es1 with scopes := prev)
 * G tn t and ghost_kept cenv es0 sa G0 tn0 s0 G tn.  For every actual
 * decoded INVOKE (lbl,arg_ops,argv), set calleePG = MAP (op_prov G) arg_ops.
 * Require EVERY (\op. op_taint tn op = {}) arg_ops; for every corresponding
 * package/setup carry intcall_entry_memory ce params penv argbase calleePG
 * (tn with t_var := FEMPTY) setup and intcall_entry_return ce has_rb
 * callee_d calleePG setup.  Here argbase = if has_rb then 1 else 0 and
 * callee_d = if has_rb then SOME (HD argv,type_memory_size rtv) else NONE.
 * Keep the fresh allocation witnesses for EVERY outgoing memory site,
 * including the return buffer.  Each whole site must be disjoint from
 * P = intcall_protected cenv es0 sa s0, not just its value footprint.
 *
 * Producers: eager compile_stage_intcall_args compiles and copies each
 * memory argument before continuing.  At the next argument its buffer is
 * an older nonlocal allocation, so that argument's ghost_kept protects
 * its bytes and provenance.  The return buffer is protected the same way.
 * intcall_bound_argument_layout supplies the declared slot size;
 * intcall_separated_site_outside publishes whole-site separation.
 * S1 intcall_entry alone supplies neither provenance nor robustness.
 *
 * CALLEE: quantify over the actual gas_invoke_entry and decoded operands,
 * not a separately chosen callee or parameter ghost.  Starting with
 * FEMPTY and tn with t_var := FEMPTY, compose the prologue's counted path
 * with the body IH and frame_ret_ok_ptr at callee_d and intret_ptr_q.
 * compile_internal_prologue_entry_ptr supplies ghost_inv and the counted
 * entry path.  Source selection supplies no defaults, nr=F, and the IH
 * for the pushed context.  body_sim_mutual supplies the S1 body facts.
 * The runtime package uses use_trans=T; its constructed environment and
 * prologue preserve this ce_nonreentrant component.  Prologue capture
 * replaces the MemLoc return buffer by PtrVar.  These discharge the
 * transient-unlock and non-MemLoc premises of internal_frame_ret_ok_ptr.
 * intcall_entry_return_bounds supplies BOTH strict return-size bounds.
 *
 * RESTORE: require the callee's pointer outcome for every actual entry,
 * retaining the same source result, raw IntRet/abort, and gas evidence.
 * The pointer outcome's erasure and gas_path_exit identify a raw run;
 * gasPathPtrExec.gas_path_ptr_exec provides its ghost and pointer safety.
 * Use the S1 exit's concrete-memory frame only on that same raw result,
 * never on an unrelated existential execution.  The successful post must
 * be vv_post plus ghost_inv, ptr_vv_ok, ptr_buf_ok and ghost_kept, exactly
 * as expr_vv_sim_ptr_def; abort post is expr_exit with no ghost invariant.
 *
 * For the ghost frame instantiate intcall_run_mem_frame at P above:
 * setup resets local allocas/G; PG is built from the actual separated
 * operands; the compiler supplies lowering_context_ok, and the caller
 * pointer precondition supplies no-DALLOCA.  Empty callee t_var gives
 * intcall_word_taint_empty.  Confinement covers all local bytes of P.
 * Restore caller G via ghost_step_invoke, whose outputs have no provenance
 * or variable taint; combine the concrete S1 frame and nonincreasing
 * protected t_mem to recover robustness, not from either frame alone.
 * Store stack-return words into the fresh return site on the rc>0 path.
 * Compose counted paths with gas_path_ptr_then, preserving the actual
 * gas marks.  Value-only gas_outcome is NOT a pointer outcome producer.
 *
 * This audit identifies construction/proof obligations, not additional
 * admitted facts.  No missing external premise was found by inspection.
 *)

(* ADMITTED: a piece of the body induction. *)
Theorem body_intcall_case_ptr:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' vs t'4' needed_dflts cxd s'7' prev
         t'5' s'8' dflt_vs t'6' all_tenv s'9' env t'7' s'10' rtv
         t'8' is_view s'11' x'' t'9' s'12' cxf t'10'.
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
       eval_exprs cx es s'6' = (INL vs,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       finally
         (ignore_bind (set_scopes [FEMPTY]) (eval_exprs cxd needed_dflts))
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'9' = (INL env,t'7') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'10' =
       (INL rtv,t'8') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'11' = (INL x'',t'9') /\
       push_function (src_id_opt,fn) env cx s'12' = (INL cxf,t'10') ==>
       body_stmts_ptr_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts sstup2
         ret body' s'5' x' t'3' s'6' vs t'4' needed_dflts cxd s'7' prev
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
       eval_exprs cx es s'6' = (INL vs,t'4') /\
       needed_dflts = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
       cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
       get_scopes s'7' = (INL prev,t'5') /\
       set_scopes [FEMPTY] s'8' = (INL x'',t'6') ==>
       body_exprs_ptr_ok cxd needed_dflts) /\
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
       body_exprs_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  cheat
QED
