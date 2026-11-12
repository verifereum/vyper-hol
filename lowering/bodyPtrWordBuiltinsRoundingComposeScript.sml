(* Decimal operand composition for both rounding builtins. *)
Theory bodyPtrWordBuiltinsRoundingCompose
Ancestors bodyPtrWordBuiltinsRoundingContinue bodyPtrWordBuiltinsTypedShapes
  bodyPtrWordBuiltinsNotCompose bodyPtrWordBuiltinsWitnessCompose
  typedWordArgsFactsPtr bodyPtrPreds bodyPtrDefs exprSimSource exprSimHypsDefs
  exprSimUnopProps exprSimUnopComposeProps exprPtrUnwrap gasSummaryComposePtr
  gasExemptCert exprSimDefs exprSimProps loweringPosts exprLoweringProps
  exprLowering compileEnv vyperInterpreter vyperState vyperAST vyperTypeSystem
  exprUnopStraight fragGasFresh freshWrites vyperTyping fragExec builtinProps vyperContext
  exprSimWordBuiltins exprSimBuiltins

Theorem word_round_lower:
  lower_value compile_expr cenv ty (Builtin ann (if up then Ceil else Floor) [e]) sa = (op,sb) ==>
  ?x s1. lower_value compile_expr cenv ty e sa = (x,s1) /\
    (if up then compile_ceil else compile_floor) x 10000000000 s1 = (op,sb)
Proof
  Cases_on `up` >> simp[] >> metis_tac[lower_value_ceil, lower_value_floor]
QED

Theorem word_round_stack:
  compile_expr cenv ty (Builtin ann (if up then Ceil else Floor) [e]) sa = (vv,sb) ==>
  ?op. vv = StackValue ann op
Proof
  Cases_on `up` >> simp[] >> strip_tac
  >- metis_tac[compile_ceil_stack] >>
  irule compile_word_builtin_stack >> goal_assum (drule_at Any) >> simp[]
QED

Theorem word_round_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann (if up then Ceil else Floor) [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx ty e es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (if up then Ceil else Floor) [e]) es
Proof
  strip_tac >>
  `expr_type e = BaseT DecimalT /\ ann = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es` by
    (irule word_rounding_operand_pre >> qexists_tac `if up then Ceil else Floor` >>
     simp[] >> Cases_on `up` >> simp[]) >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule word_round_lower >> strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `straight_fresh ((if up then compile_ceil else compile_floor) x 10000000000)` by
    (Cases_on `up` >> simp[straight_fresh_ceil, straight_fresh_floor]) >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`ann`, `if up then Ceil else Floor`] >>
     Cases_on `up` >> gvs[builtin_args_length_ok_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all word_operand_ptr_facts >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ Qfacts _` >>
  `bind (eval_expr cx (Builtin ann (if up then Ceil else Floor) [e])) (read_result cx) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v es. (unop_result cx ann (if up then Ceil else Floor) [expr_type e] v es,es))` by
    (irule eval_expr_unop_action_general >> Cases_on `up` >> simp[builtin_args_length_ok_def]) >>
  gvs[] >> irule gas_outcome_ptr_bind_mid >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\v ee G tn t.
    expr_post ctx func cenv cx e es sa s1 s0 ee v x t /\
    t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\ ptr_val_ok cx (expr_type e) v x G tn t /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\ ~t.vs_halted /\
    (?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v)` >>
  reverse conj_tac
  >- (irule gas_outcome_ptr_conseq >>
      qexistsl_tac [`Qfacts`, `\res ee gt r. expr_exit res r`] >>
      simp[Abbr `Qfacts`] >> rpt strip_tac >> gvs[] >> Cases_on `res` >> gvs[expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> simp[expr_type_def, is_word_type_def] >> strip_tac >>
  ho_match_mp_tac word_round_expr_outcome >>
  gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def] >> metis_tac[]
QED

Theorem body_word_round_singleton_ptr_ok:
  !cx ann e up. body_expr_ptr_ok cx e ==>
    body_expr_ptr_ok cx (Builtin ann (if up then Ceil else Floor) [e])
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_type e = BaseT DecimalT /\ ann = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es` by
    (irule word_rounding_operand_pre >> qexists_tac `if up then Ceil else Floor` >>
     simp[] >> Cases_on `up` >> simp[]) >>
  `expr_sim_ptr d ctx PG func cenv cx ty e es` by
    (qpat_x_assum `body_expr_ptr_ok _ _` mp_tac >>
     simp[body_expr_ptr_ok_def] >> metis_tac[]) >>
  drule_all word_round_sim_ptr >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_vv_sim_ptr_stack >> simp[] >>
  conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty
        (Builtin (BaseT (IntT 256)) (if up then Ceil else Floor) [e]) sa` >>
      drule word_round_stack >> strip_tac >> simp[] >> metis_tac[]) >>
  metis_tac[eval_expr_builtin_value]
QED
