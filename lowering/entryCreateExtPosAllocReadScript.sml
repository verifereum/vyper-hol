(* The allocating positional snapshot reads the value from the selected VV
   child, at that child's source and machine endpoints. *)
Theory entryCreateExtPosAllocRead
Ancestors
  entryCreateFocusSpec stmtReasonVvMemory exprSimIfExpWidenedPhysicalType
  exprSimHyps aggregateEvaluatedLayout vyperStorageFootprint vyperState

Theorem extcall_pos_alloc_read_inputs:
  expr_body_pre ce cx env e es /\ ~is_word_type (lowered_value_type ce e) /\
  (!tail. eval_expr cx e (es with gas_obs := xs ++ tail) =
          (res,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at si s /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,func) ce cx e (es,sa,si,s0,vv,G0,tn0)
      H res ee G tn s) ==>
  ?raw v. res = INL raw /\
    eval_expr cx e (es with gas_obs := xs ++ ee.gas_obs) = (INL raw,ee) /\
    read_result cx raw ee = (INL v,ee) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func ce cx e es sa si s0 ee raw vv s /\
      ghost_inv_at (DF H) lo d ce cx ee G tn s) /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    s.vs_current_bb = si.cs_current_bb /\ s.vs_inst_idx = LENGTH si.cs_current_insts /\
    vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv s /\
    ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
    (!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G s) /\
    (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G s) /\
    (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
      ?val. read_result cx raw ee = (INL val,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
               eval_operand (vv_operand vv) s = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory rt val (w2n w) mem)) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  strip_tac >>
  `~is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits,arg_type_fits_word_type] >>
  drule_all_then assume_tac post_value_type_nonword >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> create_operand_vv_post _ _ _ _ _ _ _ _ _ _ _`
    (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def])) >>
  drule_then (qx_choose_then `v` assume_tac) vv_post_read_ok >>
  `eval_expr cx e (es with gas_obs := xs ++ ee.gas_obs) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr cx e _ = _` (qspec_then `ee.gas_obs` mp_tac) >>
     simp[evaluation_state_component_equality]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post H ctx func ce cx e es sa si s0 ee tv vv s /\
     ghost_inv_at (DF H) lo d ce cx ee G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!h. valid_horizon _ _ _ _ ==> create_operand_vv_post _ _ _ _ _ _ _ _ _ _ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [create_operand_vv_post_def])) >>
     fs[]) >>
  qexistsl_tac [`tv`,`v`] >> fs[create_operand_at_def]
QED
