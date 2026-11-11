(* Resource-preserving framed array producer. *)
Theory bodyIntCallFamAggSubscriptArrayProducer
Ancestors
  bodyIntCallFamAggSubscriptArraySetup bodyIntCallFamAggSubscriptArraySequence
  bodyIntCallFamAggSubscriptArrayAdapter
  bodyIntCallFamAggSubscriptArrayCompose bodyIntCallFamAggSubscriptArrayPrepare
  bodyIntCallFamAggSubscriptPosts bodyIntCallJointContract
  bodyIntCallFamAggSubscriptGas bodyIntCallFamStmtExitBoundary
  exprSimSubscriptArray exprSimSubscriptArraySource exprSimHypsDefs
  exprLoweringProps gasOutcome gasSummary loweringPosts

Theorem intcall_subscript_array_framed_producer:
  intcall_expr_producer fp obj /\ intcall_forced_producer fp idx /\
  place_type ce obj = ValPT (ArrayT et bd) /\ 
    post_value_type ce obj = expr_type obj /\
    ((~ce.ce_is_ctor /\
      !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode) \/
     ((?n. bd = Fixed n) /\
      (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
      !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocMemory)) /\ 
  expr_type obj = ArrayT et bd /\
  (!t r t'. eval_expr fp.jc_cx idx t = (INL r,t') ==>
    t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
  (!s tr slot vt t. eval_expr fp.jc_cx obj s <>
    (INL (PlaceR (StoragePlace tr slot vt)),t)) /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es /\
  supportedExprs$supported_expr fp.jc_tops obj /\
  supportedExprs$supported_expr fp.jc_tops idx /\ 
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
  drule_all expr_body_pre_array_subscript_base >> strip_tac >>
  drule_all exprSimSubscriptArrayFramedTheory.compile_expr_array_subscript >> strip_tac >>
  drule_all intcall_array_compile_cuts >> strip_tac >>
  `gas_admissible (eval_expr fp.jc_cx obj) expr_vv_res_ok es` by
    (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     metis_tac[exprSimSourceTheory.expr_body_pre_gas_obs,
               exprSimSourceTheory.expr_body_pre_vv_res_ok]) >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr obj) /\
   calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr idx)` by
    fs[vyperTypeCallGraphTheory.int_calls_expr_def,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_append] >>
  qpat_x_assum `intcall_expr_producer _ _` mp_tac >>
  rewrite_tac[intcall_expr_producer_def] >> disch_then drule_all >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume intcall_subscript_array_framed_producer[exit]:
  Cases_on `res` >- fs[exprSimDefsTheory.expr_exit_def] >> rename1 `INR exc` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  conj_tac
  >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
      first_assum ACCEPT_TAC) >> fs[]
QED
Resume intcall_subscript_array_framed_producer[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  pure_once_rewrite_tac[eval_expr_subscript_bind] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED
Resume intcall_subscript_array_framed_producer[normal]:
  qpat_x_assum `(\res ee u. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  pure_rewrite_tac[GSYM gas_outcome_def] >>
  irule intcall_framed_array_after_base >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  qexists_tac `env` >>
  reverse conj_tac >- suspend "index_entry" >>
  suspend "suffix"
QED

Resume intcall_subscript_array_framed_producer[index_entry]:
  `eval_expr fp.jc_cx obj
     (es with gas_obs := gas_explicit marks s.vs_gas_readings) =
     (INL tv,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre ce fp.jc_cx env idx (es_end with gas_obs := [])` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  fs[intcall_expr_cont_def] >>
  simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
  `expr_body_pre ce fp.jc_cx env idx (es_end with gas_obs := gs)` by fs[] >>
  drule_all (REWRITE_RULE [ETA_THM] exprSimSourceTheory.expr_body_pre_res_ok) >> simp[]

QED

Resume intcall_subscript_array_framed_producer[suffix]:
  rpt gen_tac >> strip_tac >>
  `?p. bvv = LocatedValue (ArrayT et bd) p` by
    (`vv_location bvv = SOME LocCode \/ vv_location bvv = SOME LocMemory` by
       metis_tac[pairTheory.FST] >>
     Cases_on `bvv` >> gvs[contextTheory.vv_location_def] >>
     fs[loweringPostsTheory.vv_holds_def, compileEnvTheory.is_bytestring_type_def]) >>
  qpat_x_assum `bvv = _` SUBST_ALL_TAC >>
  drule_all intcall_array_subscript_annotation >> strip_tac >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  simp[contextTheory.vv_location_def, contextTheory.vv_operand_def,
       arithmeticTheory.ADD_COMM] >>
  irule (SRULE [contextTheory.vv_operand_def, contextTheory.vv_location_def,
                arithmeticTheory.ADD_COMM] intcall_array_producer_suffix) >>
  simp[SF SFY_ss, contextTheory.vv_operand_def, contextTheory.vv_location_def,
       bodyIntCallFamAggStructFieldsTheory.intcall_expr_cont_end_gas_obs] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ (eval_expr _ obj) _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[SF SFY_ss, contextTheory.vv_operand_def, contextTheory.vv_location_def,
       arithmeticTheory.ADD_COMM, compileEnvTheory.is_word_type_def,
       compileEnvTheory.is_bytestring_type_def] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  fs[contextTheory.vv_operand_def, contextTheory.vv_location_def,
     loweringPostsTheory.vv_storage_live_def, compileEnvTheory.is_word_type_def,
     compileEnvTheory.is_bytestring_type_def]
QED

Finalise intcall_subscript_array_framed_producer
