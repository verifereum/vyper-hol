Theory exprSimAbiDecodeCompose
Ancestors
  exprSimAbiDecodeCallerSuffix exprSimAbiDecodeBodySuccess
  exprSimAbiDecodeEntryTyping exprSimHyps exprOpenFirstOperand
  exprSimSource exprSimDefs exprSimHypsDefs gasSummaryCompose gasSummary gasExemptCert
  gasOutcome gasNormalPrefix vyperState vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTyping vyperValue compileEnv loweringPosts

Theorem abi_decode_child_exit_summary:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INR exc) ee r /\ exit_result r /\ expr_exit (INR exc) r ==>
  gas_summary_at F (ctx,func) marks
    (eval_expr cx (TypeBuiltin ty (AbiDecode unwrap) ty [e])) (es,s0) Q
    (\res es1 r. expr_exit res r)
Proof
  strip_tac >> rewrite_tac[abi_decode_singleton_source, gas_summary_at_def] >>
  qexistsl_tac [`INR exc`, `ee`, `r`] >> simp[] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> Cases_on `exc` >> Cases_on `r` >>
  gvs[expr_exit_def] >> Cases_on `e'` >> gvs[expr_exit_def]
QED

Theorem abi_decode_child_exempt_cert:
  gas_exempt_cert memory tops p
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (eval_expr cx (TypeBuiltin ty (AbiDecode unwrap) ty [e])) (return ()))
    start marks out endpoint
Proof
  strip_tac >> rewrite_tac[abi_decode_singleton_source] >>
  `ignore_bind
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]))
        (\w. return (Value w)))) (return ()) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. ignore_bind
        (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]))
          (\w. return (Value w))) (return ()))` by
    (qmatch_goalsub_abbrev_tac `bind a _` >>
     simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `a x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem abi_decode_normal_prefix_summary:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  expr_post ctx func ce cx e es sa start s0 (ee with gas_obs := []) v data s /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  gas_summary_at F (ctx,func) marks
    (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty [e])) (es,s0)
    (\res es1 t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
        es1 tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts)
    (\res es1 r. expr_exit res r)
Proof
  strip_tac >>
  `expr_body_pre ce cx env e es` by
    metis_tac[expr_body_pre_type_builtin_head] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_result_typed env e (Value v)` by
    (irule (cj 3 expr_body_pre_eval) >>
     qexistsl_tac [`ce`, `cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee with gas_obs := []`] >> fs[bind_def]) >>
  `?bs. v = BytesV bs` by
    (`env.type_defs = get_tenv cx` by
       metis_tac[abi_decode_inv_type_env, expr_body_pre_def] >>
     fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
     Cases_on `v` >> gvs[value_has_type_def]) >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule abi_decode_observed_scopes_dom >> simp[]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (data,start)` by metis_tac[] >>
  drule_all abi_decode_caller_suffix_summary >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  `ann = ty` by
    metis_tac[abi_decode_parent_type, expr_body_pre_def] >>
  pop_assum SUBST_ALL_TAC >>
  rewrite_tac[abi_decode_singleton_source] >>
  qexistsl_tac [`res`, `es_end`, `r`] >>
  (conj_tac
   >- (irule (SRULE [] (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
       goal_assum (drule_at Any) >> metis_tac[]) >>
   gvs[] >> metis_tac[])
QED
