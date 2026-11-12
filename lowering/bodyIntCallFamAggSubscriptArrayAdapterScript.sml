(* Convert counted child endpoints to the exact framed suffix obligation. *)
Theory bodyIntCallFamAggSubscriptArrayAdapter
Ancestors
  bodyIntCallFamAggSubscriptArraySetup bodyIntCallFamAggSubscriptArrayCompose
  bodyIntCallFamAggSubscriptArrayPrepare bodyIntCallFamAggSubscriptGas
  bodyIntCallFamStmtExitBoundary bodyIntCallJointContract
  exprSimSubscriptArraySource exprSimHypsDefs exprLoweringProps loweringPosts

Theorem intcall_array_endpoint_operands:
  expr_body_pre ce fp.jc_cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et bd /\
  compile_expr ce ty obj sa = (LocatedValue (ArrayT et bd) p,sm) /\
  lower_value compile_expr ce ty idx sm = (iop,sc) /\
  eval_expr fp.jc_cx obj es' = (INL tv,mid) /\
  (es' with gas_obs := es.gas_obs) = es /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s mid sm t /\
  intcall_expr_cont fp ce env mid sm t raw sc u ==>
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sc /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  `is_word_type (expr_type idx)` by metis_tac[intcall_array_subscript_annotation] >>
  `expr_body_pre ce fp.jc_cx env (Subscript et obj idx) es'` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs] >>
  `expr_body_pre ce fp.jc_cx env idx mid` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `et` >> simp[]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule exprSimSubscriptArrayOriginTheory.compile_array_pointer_not_label >>
     disch_then irule >> simp[] >> qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sc` by
    fs[intcall_expr_res_def, intcall_expr_cont_def] >>
  `!x. iop = Var x ==> not_fresh_at sc x` by
    (qpat_assum `lower_value _ _ _ _ _ = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `!l. iop <> Label l` by
    (drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >>
     impl_tac
     >- (conj_tac >- fs[expr_body_pre_def] >>
         metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed]) >> simp[]) >>
  fs[intcall_expr_res_def, intcall_expr_cont_def]
QED

Theorem intcall_array_producer_suffix:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type ce obj = expr_type obj /\
  ((~ce.ce_is_ctor /\
    !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
    !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocMemory)) /\
  (!t r t'. eval_expr fp.jc_cx idx t = (INL r,t') ==>
    t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!s tr slot vt t. eval_expr fp.jc_cx obj s <>
    (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
  compile_expr ce ty obj sa = (LocatedValue (ArrayT et bd) p,sm) /\
  lower_value compile_expr ce ty idx sm = (iop,sc) /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd fp.jc_func /\
  intcall_expr_res fp ce env es sa s /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func) (eval_expr fp.jc_cx obj)
    (es,s) marks (INL tv) mid (OK t) /\
  vv_holds ce fp.jc_cx (post_value_type ce obj) tv
    (LocatedValue (ArrayT et bd) p) (mid with gas_obs := []) t /\
  vv_at ce fp.jc_cx (post_value_type ce obj) sa sm (mid with gas_obs := []) tv
    (LocatedValue (ArrayT et bd) p) t /\
  (~expr_has_effect obj ==>
    vv_storage_live fp.jc_cx (LocatedValue (ArrayT et bd) p) mid t) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (p.ptr_location = LocMemory ==>
    !tv'. evaluate_type (get_tenv fp.jc_cx) (ArrayT et bd) = SOME tv' ==>
      ?w a k. eval_operand p.ptr_operand t = SOME w /\
        a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
        a + k < dimword (:256) /\
        (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
  intcall_expr_cont fp ce env es sa s mid sm t /\
  gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (bind (eval_expr fp.jc_cx idx) (read_result fp.jc_cx))
    (mid with gas_obs := [],t) imarks (INL v) raw (OK u) /\
  expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx idx (mid with gas_obs := []) sm sc t
    (raw with gas_obs := []) v iop u /\
  intcall_expr_cont fp ce env mid sm t raw sc u ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (select_result fp.jc_cx (ArrayT et bd) tv (ValueSubscript v))
    (raw with gas_obs := [],u)
    (\res ee q. ?tv'. res = INL tv' /\
      vv_holds ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) tv'
        (LocatedValue et (mk_ptr dst p.ptr_location)) ee q /\
      vv_at ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) sa sd ee tv'
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      (post_value_type ce (Subscript et obj idx) <> expr_type (Subscript et obj idx) ==>
        vv_own ce fp.jc_cx (post_value_type ce (Subscript et obj idx)) sa sd ee tv'
          (LocatedValue et (mk_ptr dst p.ptr_location)) q) /\
      (~expr_has_effect (Subscript et obj idx) ==>
        vv_storage_live fp.jc_cx (LocatedValue et (mk_ptr dst p.ptr_location)) ee q) /\
      (!x. vv_operand (LocatedValue et (mk_ptr dst p.ptr_location)) = Var x ==>
        not_fresh_at sd x) /\
      (post_value_type ce (Subscript et obj idx) <> NoneT /\
       ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
       ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) /\
       (case LocatedValue et (mk_ptr dst p.ptr_location) of StackValue _ _ => T
         | LocatedValue _ p => p.ptr_location = LocMemory) ==>
       !tv'. evaluate_type (get_tenv fp.jc_cx)
         (post_value_type ce (Subscript et obj idx)) = SOME tv' ==>
         ?w a k. eval_operand (vv_operand (LocatedValue et (mk_ptr dst p.ptr_location))) q = SOME w /\
           a <= w2n w /\ w2n w + type_memory_size tv' <= a + k /\
           a + k < dimword (:256) /\
           (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a + k <= b + z)) /\
      intcall_expr_cont fp ce env es sa s ee sd q)
    (\res ee out. expr_exit res out)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all intcall_array_children_source >> strip_tac >>
  qpat_assum `compile_expr _ _ obj sa = _`
    (mp_then Any (qspecl_then [`et`,`fp.jc_cx`,`bd`] mp_tac)
      intcall_array_pointer_regime) >>
  (impl_tac >- simp[]) >> disch_then assume_tac >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sm s
      (mid with gas_obs := []) tv (LocatedValue (ArrayT et bd) p) t` by
    (irule intcall_expr_endpoint_vv_post >>
     simp[Excl "vv_storage_live_def", SF SFY_ss,
          bodyIntCallFamAggStructFieldsTheory.intcall_expr_cont_end_gas_obs]) >>
  `local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sc /\
   (!l. p.ptr_operand <> Label l) /\
   (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l)` by
    (irule intcall_array_endpoint_operands >>
     conj_tac >- metis_tac[] >>
     qpat_assum `eval_expr _ _ (_ with gas_obs := _ ++ _) = _`
       (irule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     simp[SF SFY_ss,
          intcall_expr_cont_initial_gas_obs,
          bodyIntCallFamAggStructFieldsTheory.intcall_expr_cont_end_gas_obs] >>
     goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `intcall_expr_res _ _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
     simp[SF SFY_ss]) >>
  `raw.scopes = mid.scopes /\ raw.immutables = mid.immutables` by
    (qpat_x_assum `!t r t'. eval_expr _ idx _ = _ ==> _` drule >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_x_assum `eval_expr _ obj _ = _`
      (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  qpat_assum `eval_expr _ obj _ = _`
    (mp_then (Pat `eval_expr _ _ _ = _`) mp_tac intcall_framed_array_child_suffix) >>
  simp[NoAsms, exprSimPropsTheory.vv_post_initial_gas,
       exprSimSubscriptArrayComposeTheory.vv_post_final_gas,
       exprSimSubscriptArrayComposeTheory.expr_post_initial_gas,
       intcall_expr_cont_initial_gas_obs,
       bodyIntCallFamAggStructFieldsTheory.intcall_expr_cont_end_gas_obs,
       bodyIntCallFamAggStructFieldsTheory.intcall_joint_res_gas_obs] >>
  disch_then irule >> simp[SF SFY_ss] >>
  (conj_tac >- metis_tac[]) >>
  qexistsl_tac [`iop`,`sm`,`sc`,`t`] >>
  simp[exprSimSubscriptArrayComposeTheory.expr_post_initial_gas,
       bodyIntCallFamAggStructFieldsTheory.intcall_expr_cont_end_gas_obs] >>
  fs[exprSimSubscriptArrayComposeTheory.expr_post_initial_gas,
     exprSimSubscriptArrayComposeTheory.vv_post_final_gas,
     arithmeticTheory.ADD_COMM]
QED
