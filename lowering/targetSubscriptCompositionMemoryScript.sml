(* Concrete counted subscript constructor. *)
Theory targetSubscriptCompositionMemory
Ancestors
  targetSubscriptBindMemory targetSubscriptContinuationMemory targetCompilerOpenness

Theorem target_subscript_case_mem:
  !nocalls ctx func cenv cx bt e tops.
    (!env es.
      target_pre cenv cx env bt es /\
      (nocalls ==> int_calls_target bt = []) ==>
      !vt sa sb op s0.
        type_place_target env bt = SOME vt /\
        compile_get_target_ptr compile_expr cenv bt sa = (op,sb) /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        gas_admissible (eval_base_place cx bt) target_res_ok es /\
        stmt_state_rel ctx func cenv cx es s0 /\
        alloca_history func s0 /\ ~s0.vs_halted /\
        s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome T (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
          (\res ee t. ?pv. res = INL pv /\
            target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
            (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
              slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
              storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
            t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
          (\res ee r. expr_exit res r)) /\
    ((?s pv s1. eval_base_place cx bt s = (INL pv,s1)) ==>
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_sim_mem ctx func cenv cx ty e es) /\
      (!env ty es. expr_body_pre cenv cx env e es /\
        (nocalls ==> int_calls_expr e = []) ==>
        expr_vv_sim_mem ctx func cenv cx ty e es)) /\
    body_inv tops ctx cenv cx /\
    EVERY (supported_expr tops) (target_indices (SubscriptTarget bt e)) ==>
    !env es.
      target_pre cenv cx env (SubscriptTarget bt e) es /\
      (nocalls ==> int_calls_target (SubscriptTarget bt e) = []) ==>
      !vt sa sb op s0.
        type_place_target env (SubscriptTarget bt e) = SOME vt /\
        compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (op,sb) /\
        fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
        local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
        gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
        stmt_state_rel ctx func cenv cx es s0 /\
        alloca_history func s0 /\ ~s0.vs_halted /\
        s0.vs_current_bb = sa.cs_current_bb /\
        s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
        gas_outcome T (cx_tops cx) (ctx,func)
          (eval_base_place cx (SubscriptTarget bt e)) (es,s0)
          (\res ee t. ?pv. res = INL pv /\
            target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
            (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
              slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
              storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
            t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
          (\res ee r. expr_exit res r)
Proof
  match_mp_tac target_subscript_case_mem_from_boundaries >>
  conj_tac
  >- (rpt gen_tac >> MATCH_ACCEPT_TAC target_subscript_base_continuation_mem) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC target_compiler_open
QED
