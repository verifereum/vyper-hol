(* Concrete Not composition: source facts are attached to the very same
   counted pointer endpoint, never to an independently erased run. *)
Theory bodyPtrWordBuiltinsNotCompose
Ancestors
  bodyPtrWordBuiltinsNotCase bodyPtrWordBuiltinsWitnessCompose
  typedWordArgsFactsPtr bodyPtrPreds bodyPtrDefs exprSimSource exprSimHypsDefs
  exprSimUnopProps exprSimUnopComposeProps exprPtrUnwrap gasSummaryComposePtr
  gasExemptCert exprSimDefs exprSimProps loweringPosts exprLoweringProps
  exprLowering compileEnv vyperInterpreter vyperState vyperAST vyperTypeSystem
  exprUnopStraight fragGasFresh freshWrites vyperTyping fragExec builtinProps vyperContext

Theorem word_operand_ptr_facts:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\
      (!v. rr = INL v ==> ?tv.
        evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v) /\
      ee.gas_obs = [] /\ ~t.vs_halted) R
Proof
  strip_tac >> ho_match_mp_tac gas_outcome_ptr_source_facts >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >> gen_tac >> disch_tac >> gvs[] >>
  irule expr_body_pre_word_value >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`cenv`, `env`] >> simp[] >>
  qexistsl_tac [`es with gas_obs := gs`, `ee`] >> simp[] >>
  fs[bind_def]
QED

Theorem word_flag_members:
  expr_body_pre cenv cx env e es /\
  evaluate_type (get_tenv cx) (FlagT nsid) = SOME (FlagTV m) ==>
  cenv.ce_flag_n_members (nsid_to_string nsid) = m
Proof
  simp[expr_body_pre_def, expr_sim_inv_def] >> rpt strip_tac >>
  first_x_assum irule >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()]
QED

Theorem word_not_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann Not [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann Not [e]) es
Proof
  strip_tac >> drule word_not_operand_pre >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `is_word_type (expr_type e)` by
    (drule not_type_cases >> strip_tac >> gvs[is_word_type_def]) >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_not >> strip_tac >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `straight_fresh (if expr_type e = BaseT BoolT then emit_op ISZERO [x]
    else compile_invert x (expr_type e) cenv)` by
    simp[straight_fresh_not] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`expr_type e`, `Not`] >>
     simp[builtin_args_length_ok_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all word_operand_ptr_facts >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ Qfacts _` >>
  simp[eval_expr_unop_action_general, builtin_args_length_ok_def] >>
  irule gas_outcome_ptr_bind_mid >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\v ee G tn t.
    expr_post ctx func cenv cx e es sa s1 s0 ee v x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\ ptr_val_ok cx (expr_type e) v x G tn t /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\ ~t.vs_halted /\
    (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)` >>
  reverse conj_tac
  >- (irule gas_outcome_ptr_conseq >>
      qexistsl_tac [`Qfacts`, `\res ee gt r. expr_exit res r`] >>
      simp[Abbr `Qfacts`] >> rpt strip_tac >> gvs[] >>
      Cases_on `res` >> gvs[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> simp[expr_type_def] >> strip_tac >>
  ho_match_mp_tac word_not_typed_ptr_outcome >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> irule word_flag_members >>
      goal_assum (drule_at Any) >> gvs[]) >>
  gvs[expr_post_def, expr_val_rel_def]
QED

Theorem body_word_not_singleton_ptr_ok:
  !cx ann e. body_expr_ptr_ok cx e ==> body_expr_ptr_ok cx (Builtin ann Not [e])
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule word_not_operand_pre >> simp[]) >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_ptr_ok _ _` mp_tac >>
     simp[body_expr_ptr_ok_def] >> metis_tac[]) >>
  drule_all word_not_sim_ptr >> disch_then (qspec_then `ty` assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_ptr_stack >> simp[] >>
  conj_tac
  >- simp[compile_not_abs_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
