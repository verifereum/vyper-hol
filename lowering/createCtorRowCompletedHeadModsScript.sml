(* Choose the saved witnesses for one completed constructor row. *)
Theory createCtorRowCompletedHeadMods
Ancestors
  createCtorSavedSimpleMods createCtorRowCutsMods vyperStorageFootprint

Theorem ctor_row_completed_head_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,sb) /\
  vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!K. valid_horizon cx st0 K es.storage_trace ==>
    storage_well_formed_on cx es (FST K)) /\
  (is_word_type (lowered_value_type ce e) ==>
    ?G tn. !K op. valid_horizon cx st0 K ee.storage_trace /\
      lower_value compile_expr ce (expr_type e) e sa = (op,sb) ==>
      expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
        (es,sa,sb,s,op,g,h) K (INL v : value + exception) ee G tn t) /\
  (~is_word_type (lowered_value_type ce e) /\ ~exprs_can_mutate ce xs ==>
    ?G tn. !K. valid_horizon cx st0 K ee.storage_trace ==>
      ?raw. eval_expr cx e es = (INL raw,ee) /\
        vv_post_mods K ctx func ce cx e es sa sm s ee raw vv t /\
        vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv t /\
        ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF K) lo d ce cx ee G tn t /\
        ghost_kept_at lo ce es sa g h s G tn /\
        (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e op G t) /\
        (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p.ptr_operand G t) /\
        (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx raw ee = (INL val,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                  eval_operand (vv_operand vv) t = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))) /\
  (~is_word_type (lowered_value_type ce e) /\ exprs_can_mutate ce xs ==>
    ?G tn. !K. valid_horizon cx st0 K ee.storage_trace ==>
      extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [sv]
        sa sb es s g h K (INL [v] : value list + exception) ee G tn t) ==>
  ?G tn. !K. valid_horizon cx st0 K ee.storage_trace ==>
    extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [sv]
      sa sb es s g h K (INL [v] : value list + exception) ee G tn t
Proof
  strip_tac >> Cases_on `is_word_type (lowered_value_type ce e)` >> fs[]
  >- (qmatch_asmsub_rename_tac `expr_sim_full_post_mods _ _ _ _ _ _ _ _ G tn _` >>
      qexistsl [`G`,`tn`] >> rpt strip_tac >>
      irule ctor_saved_head_simple_mods >>
      qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
      qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
      qexists_tac `es.gas_obs` >> simp[]) >>
  Cases_on `exprs_can_mutate ce xs`
  >- (qpat_x_assum `exprs_can_mutate ce xs ==> _` mp_tac >> simp[]) >>
  fs[] >>
  qmatch_asmsub_rename_tac `ghost_inv_at_mods _ _ _ _ _ _ G tn _` >>
  qexistsl [`G`,`tn`] >> qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all_then ACCEPT_TAC ctor_rows_read_horizon_mods) >>
  `storage_well_formed_on cx es (FST H)` by simp[] >>
  `valid_horizon cx es H ee.storage_trace` by fs[valid_horizon_def] >>
  irule ctor_saved_head_simple_mods >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >>
  qexists_tac `es.gas_obs` >> simp[]
QED
