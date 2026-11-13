(* Signed bytestring conversion with pointer-safe selector multiplication. *)
Theory bodyPtrTypeBuiltinsResidual
Ancestors
  bodyPtrPreds vyperAST vyperInterpreter vyperTypeSystem
  bodyPtrSignedConvertConvertEntry bodyPtrSignedConvertSignedCompose
  bodyPtrWordBuiltinsWitnessCompose typedWordArgsFactsPtr exprPtrUnwrap
  exprSimConvert exprSimConvertFromBytes exprLoweringProps exprSimHyps
  gasExemptCert gasSummaryComposePtr fragGasFresh freshWrites
  externalEntryShape bodyPtrDefs compileEnv loweringStateRelDefs fragExec gasOutcomeMarkedPtr

Theorem signed_bytestring_convert_residual:
  !cx v11 tb typ es.
    (tb = Empty \/ tb = MaxValue \/ tb = MinValue \/ tb = Epsilon \/
     tb = Convert \/ tb = Extract32) /\
    (type_builtin_args_length_ok tb (LENGTH es) ==> body_exprs_ptr_ok cx es) /\
    (tb = Convert /\
     (?e. es = [e] /\ is_bytestring_type (expr_type e)) /\
     ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) ==>
    body_expr_ptr_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?e. _` strip_assume_tac >> gnvs[] >>
  `body_expr_ptr_ok cx e` by
    gvs[vyperContextTheory.type_builtin_args_length_ok_def, body_exprs_ptr_ok_def] >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `v11 = typ` by metis_tac[signed_convert_body_entry] >> gnvs[] >>
  `expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin typ Convert typ [e]) es` by
    suspend "lower" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_ptr_stack >> simp[] >> conj_tac
  >- (gen_tac >> irule compile_convert_stack) >>
  metis_tac[eval_expr_type_builtin_value]
QED

Resume signed_bytestring_convert_residual[lower]:
  simp[bodyPtrDefsTheory.expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all signed_convert_child_compile >> strip_tac >>
  `cs_extends sa s1` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 sb` by
    (qpat_x_assum `if _ then _ else _` mp_tac >>
     IF_CASES_TAC >- simp[cs_extends_def] >> strip_tac >>
     qspecl_then [`x`,`mk_convert_op (expr_type e) typ`,`s1`] mp_tac
       (cj 1 compile_type_convert_labels) >> simp[]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  drule_all signed_convert_body_entry >>
  disch_then (qspecl_then [`func`,`d`,`PG`]
    (map_every assume_tac o CONJUNCTS)) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[convert_operand_admissible] >>
  qpat_x_assum `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rewrite_tac[eval_expr_convert_action] >>
  irule gas_outcome_ptr_bind >> conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> BETA_TAC >>
      qpat_x_assum `gas_exempt_cert _ _ _ _ _ _ _ _` (ACCEPT_TAC o BETA_RULE)) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  `!res r. (?exc. res = INR exc /\ expr_exit (INR exc : value + exception) r) <=>
    expr_exit (res : value + exception) r` by
    (Cases >> simp[exprSimDefsTheory.expr_exit_def]) >>
  BETA_TAC >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >> gnvs[] >>
  qpat_x_assum `?v. rr = INL v /\ _`
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  gnvs[] >>
  drule gas_marked_exec_ptr_exec >>
  simp[gasSummaryTheory.gas_marked_exec_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!tail. _ = (INL v,_)`
    (qspec_then `[]` assume_tac) >>
  mp_tac (Q.INST [`ann` |-> `typ`, `ee` |-> `mid with gas_obs := []`,
    `es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`]
    signed_convert_normal_packet) >>
  (impl_tac >- (simp[] >>
    qpat_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >>
    CONV_TAC (DEPTH_CONV ETA_CONV) >>
    pure_rewrite_tac[listTheory.APPEND_NIL] >> simp[])) >>
  disch_then (qx_choose_then `xx` (qx_choose_then `sm`
    (qx_choose_then `tv` (map_every assume_tac o CONJUNCTS)))) >>
  gnvs[] >>
  `is_word_type typ` by (qpat_assum `(?n. typ = _) \/ _` strip_assume_tac >>
    gvs[compileEnvTheory.is_word_type_def]) >>
  simp[vyperASTTheory.expr_type_def] >>
  drule_all signed_convert_code_entry >> strip_tac >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  irule (Q.INST [`ee` |-> `mid with gas_obs := []`]
    signed_convert_continuation_gas_actual |> SIMP_RULE (srw_ss()) []) >>
  `~t.vs_halted` by
    metis_tac[fragGasModeTheory.gas_marked_path_def, fragGasPathTheory.gas_path_normal] >>
  `local_ptrs_reserved cenv s1` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ptr_buf_ok cenv e x G t` by metis_tac[is_word_type_not_bytestring] >>
  simp[] >> conj_tac
  >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
      qpat_assum `!tail. _ = (INL v,_)` (qspec_then `[]` mp_tac) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >>
      pure_rewrite_tac[listTheory.APPEND_NIL] >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`x`,`s1`] >> simp[] >>
  conj_tac
  >- (gvs[local_ptrs_reserved_def]) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `if _ then _ else 64 <= _ /\ _` mp_tac >>
  IF_CASES_TAC >> gvs[]
QED
Finalise signed_bytestring_convert_residual
