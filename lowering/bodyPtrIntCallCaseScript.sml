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
  bodyPtrIntCallEq bodyPtrIntCallWidened
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

(* The piece of the body induction: bodyPtrIntCallEq proves the call at the
   callee's declared return type; bodyPtrIntCallWidened holds the widened
   call (RESIDUAL, posts-interface wave).
   Intuition.  Runtime only: the judgments assume ~cenv.ce_is_ctor, and
   body_inv makes it cx.in_deploy, so lookup_callable_function is the
   Internal lookup.  The S1 half of each post (expr_post, vv_post) is S1's
   reasoning (bodySimMain's body_sim_mutual covers this case at this base);
   the ghost half follows compile_call's pieces in order:
   - the arguments and defaults by their IHs (ptr_val_ok/ptr_vv_ok of each
     argument), then their staging into fresh buffers (stage_mem_arg_frag's
     ptr twin: copies into a new alloca, so the staged pointer's site is
     the alloca's);
   - the INVOKE edge: the callee's run is ptr-safe from its entry with
     PG = MAP (op_prov G) ops.  Its prologue gives each pointer parameter
     its site from PG and the return buffer's from the caller's alloca, so
     the callee's ghost_inv holds at its body's start, and the IH
     body_stmts_ptr_ok cxf body' at the callee's frame (d = the return
     buffer, RetQ carrying the ghost) gives a ptr-safe counted path to its
     IntRet, which gas_path_ptr_exec turns into the ptr_safe_blocks the
     INVOKE's ptr_safe_step asks for;
   - the return: the caller's ghost after the INVOKE is ghost_step's
     (callee taint, caller's t_var minus the outputs); the callee writes
     only above the caller's live regions (intCallFrame's
     callee_writes_above), so ghost_kept and the caller's live locals'
     ghost_inv carry over; the result (stack word, stack multi-return
     stored by store_multi_results, or the memory return buffer) is
     ptr_val_ok/ptr_vv_ok with the return buffer's site.
   One lemma per return form (stack word, stack multi-return, memory
   return, no value). *)
Theorem body_intcall_case_ptr:
  !cx v16 src_id_opt fn es v17.
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7'
         prev t'5' s'8' dflt_vs t'6' s'9' vs t'7' all_tenv s'10' env t'8'
         s'11' rtv t'9' is_view s'12' x'' t'10' s'13' cxf t'11'.
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
       finally do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od
         (set_scopes prev) s'8' = (INL dflt_vs,t'6') /\
       read_results cx results s'9' = (INL vs,t'7') /\ all_tenv = get_tenv cx /\
       lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
         "IntCall bind_arguments" s'10' = (INL env,t'8') /\
       lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'11' =
       (INL rtv,t'9') /\ (is_view <=> is_view_mut mut) /\
       lock_if_nr cx nr is_view s'12' = (INL x'',t'10') /\
       push_function (src_id_opt,fn) env cx s'13' = (INL cxf,t'11') ==>
       body_stmts_ptr_ok cxf body') /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3' s'6' results t'4' needed_dflts cxd s'7'
         prev t'5' s'8' x'' t'6'.
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
       body_exprs_ptr_ok cxd needed_dflts) /\
    (!s'' x t s'3' ts t' s'4' tup t'' mut stup nr stup2 args sstup dflts
         sstup2 ret body' s'5' x' t'3'.
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
       body_results_ptr_ok cx es) ==>
    body_expr_ptr_ok cx (Call v16 (IntCall (src_id_opt,fn)) es v17)
Proof
  rpt gen_tac >> disch_tac >>
  first_assum (assume_tac o MATCH_MP body_intcall_eq_ptr) >>
  first_x_assum (assume_tac o MATCH_MP body_intcall_widened_ptr) >>
  simp_tac std_ss [body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lowered_value_type cenv (Call v16 (IntCall (src_id_opt,fn)) es v17) =
            expr_type (Call v16 (IntCall (src_id_opt,fn)) es v17)` >>
  metis_tac[]
QED
