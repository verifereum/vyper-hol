(* Counted composition of tuple base evaluation and readonly selection. *)
Theory bodyIntCallFamAggSubscriptTupleProducer
Ancestors
  bodyIntCallFamAggSubscriptTupleSuffix bodyIntCallFamAggSubscriptPosts
  bodyIntCallFamAggSubscriptTupleSource loweringPosts
  bodyIntCallJointContract bodyIntCallJointAggCore exprSimSubscriptMap
  exprSimSource exprLoweringProps emitHelperProps fragExec gasOutcome gasSummary
  exprSimTuple exprSimHypsDefs gasContext context compileEnv exprSimAccounts
  exprLowering exprSimAttributeProps

Theorem intcall_subscript_tuple_producer:
  intcall_expr_producer fp obj /\
  place_type ce obj = ValPT (TupleT tys) /\ expr_type obj = TupleT tys /\
  post_value_type ce obj = expr_type obj /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es /\
  supportedExprs$supported_expr fp.jc_tops obj /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr (Subscript ann obj idx)) /\
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  gas_admissible (eval_expr fp.jc_cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  intcall_expr_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_expr fp.jc_cx (Subscript ann obj idx)) (es,s)
    (\res ee u. ?tv. res = INL tv /\
      vv_holds ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) tv vv ee u /\
      vv_at ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv u /\
      (post_value_type ce (Subscript ann obj idx) <> expr_type (Subscript ann obj idx) ==>
        vv_own ce fp.jc_cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv u) /\
      (~expr_has_effect (Subscript ann obj idx) ==> vv_storage_live fp.jc_cx vv ee u) /\
      (!x. vv_operand vv = Var x ==> not_fresh_at sb x) /\
      (post_value_type ce (Subscript ann obj idx) <> NoneT /\
       ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
       ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) /\
       (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce (Subscript ann obj idx)) = SOME tv' ==>
        ?w a k. eval_operand (vv_operand vv) u = SOME w /\
          a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
          a + k < dimword (:256) /\
          (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
      intcall_expr_cont fp ce env es sa s ee sb u)
    (\res ee r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  drule_all compile_expr_tuple_subscript >> strip_tac >>
  `cs_extends sa st1 /\ sa.cs_next_var <= st1.cs_next_var /\
   sa.cs_next_id <= st1.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends st1 sb` by
    (drule emit_op_extends_next_var >> simp[]) >>
  `fn_has_code sa st1 fp.jc_func /\ fn_has_code st1 sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr fp.jc_cx obj) expr_vv_res_ok es` by
    (simp[gas_admissible_def] >> rpt strip_tac >>
     metis_tac[expr_body_pre_gas_obs, expr_body_pre_vv_res_ok]) >>
  qpat_x_assum `intcall_expr_producer _ _` mp_tac >>
  rewrite_tac[intcall_expr_producer_def] >> disch_then drule_all >>
  `eval_expr fp.jc_cx (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) =
    bind (eval_expr fp.jc_cx obj)
      (\r. select_result fp.jc_cx (expr_type obj) r (ValueSubscript (IntV (&k))))` by
    simp[FUN_EQ_THM, eval_expr_tuple_subscript] >>
  qpat_assum `eval_expr _ (Subscript _ _ _) = _` (fn th => rewrite_tac[th]) >>
  disch_then (mp_then Any irule gas_outcome_bind_result_exec) >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt gen_tac >> Cases_on `res` >> simp[] >> rpt strip_tac >> simp[]) >>
      rpt gen_tac >> simp[] >> rpt strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee u. _) _ _ _` mp_tac >> simp[] >> strip_tac >>
  suspend "normal"
QED

Resume intcall_subscript_tuple_producer[normal]:
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa st1 s
     (mid with gas_obs := []) v bvv t` by
    (simp[vv_post_def] >> fs[intcall_expr_cont_def, intcall_expr_res_def] >>
     first_assum ACCEPT_TAC) >>
  `eval_expr fp.jc_cx obj (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (qspec_then `[]` mp_tac o CONJUNCT1 o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[]) >>
  `expr_body_pre ce fp.jc_cx env (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) /\
   expr_body_pre ce fp.jc_cx env obj
     (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by
    simp[expr_body_pre_gas_obs] >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) sa st1 s
     (mid with gas_obs := []) v bvv t` by
    (gvs[vv_post_def, locals_kept_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  drule_all intcall_tuple_source_selection >> strip_tac >>
  `?w. eval_operand (vv_operand bvv) t = SOME w` by
    (Cases_on `bvv` >>
     qpat_assum `vv_holds _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_holds_def, expr_val_rel_def]) >>
     simp[vv_operand_def] >> metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env es /\ local_ptrs_reserved ce sa` by
    fs[intcall_expr_res_def] >>
  `emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset ce tys (vv_loc bvv) k))]
     st1 = (p,sb)` by fs[literal_int_index_def] >>
  `vv_loc bvv = LocMemory ==>
    ?a len. a <= w2n w /\ w2n w + type_memory_size (TupleTV tvs) <= a + len /\
      a + len < dimword (:256) /\
      (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + len <= b + z)` by
    (strip_tac >>
     qpat_x_assum `~is_word_type _ /\ _ ==> _` mp_tac >>
     simp[is_word_type_def, is_bytestring_type_def] >>
     `case bvv of StackValue _ _ => T | LocatedValue bt bp => bp.ptr_location = LocMemory` by
       (Cases_on `bvv` >> gvs[vv_loc_def, vv_location_def]) >>
     simp[]) >>
  `k < LENGTH tvs` by simp[] >>
  drule_all intcall_tuple_suffix_post >>
  disch_then (qspec_then `Literal ity (IntL (&k))` strip_assume_tac) >>
  irule intcall_gas_transparent_path_outcome >>
  qexistsl_tac [`mid with gas_obs := []`, `OK u`, `INL selected`] >>
  simp[] >> conj_tac
  >- (drule tuple_select_gas_obs >> simp[]) >>
  gvs[] >> simp[vv_operand_def]
QED

Finalise intcall_subscript_tuple_producer
