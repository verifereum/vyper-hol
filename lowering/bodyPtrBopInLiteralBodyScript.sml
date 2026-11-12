Theory bodyPtrBopInLiteralBody
Ancestors
  bodyPtrBopInLiteralContinuation bodyPtrBopInLiteralCompiler
  bodyPtrBopInLiteralReady bodyPtrBopInArgsInvariant bodyPtrBopInLiteralSource
  exprSimBopInLiteralWord bodyPtrDefs bodyPtrPreds bodySim exprPtrUnwrap
  exprSimDefs exprSimWordArgs exprLoweringProps exprLowering compileEnv
  gasSummaryComposePtr gasOutcomeMarkedPtr typedWordArgsPostPtr fragGasPathPtr
  freshWrites fragExec list vyperState vyperAST exprSimHypsDefs exprSimUnopProps
  fragGasSeqPtr exprSimPrecompiles

Theorem literal_uniform_zip[local]:
  EVERY (\e. f e = tv) (args:expr list) /\ LENGTH args = LENGTH vs /\
  LIST_REL (\x ev. eval_operand x t = SOME (typed_val_to_w256 (f (FST ev)) (SND ev))) xs (ZIP (args,vs)) ==>
  LIST_REL (\x v. eval_operand x t = SOME (typed_val_to_w256 tv v)) xs vs
Proof
  strip_tac >> gvs[LIST_REL_EL_EQN, EVERY_EL, EL_ZIP] >> metis_tac[]
QED

Theorem literal_expr_sim_ptr:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray aet n) elems]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  body_exprs_ptr_ok cx (e1::elems) /\ body_inv tops ctx cenv cx ==>
  expr_sim_ptr d ctx PG fn cenv cx ty
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray aet n) elems]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_body_evaluate_types >> strip_tac >>
  drule_all literal_body_action_flat >> disch_tac >>
  drule_all literal_body_typing >> strip_tac >>
  `is_ArrayT a` by simp[is_ArrayT_def] >>
  `wb_args_shape cenv expr_type (e1::elems)` by
    metis_tac[literal_args_shape] >>
  drule_all literal_ptr_args_ready >>
  disch_then (qspecl_then [`fn`,`d`,`PG`] assume_tac) >>
  drule literal_semantic_args_ready >> simp[] >> disch_tac >>
  rewrite_tac[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  gnvs[] >> drule_at (Pat `lower_value _ _ _ _ _ = _`) literal_lower_value >>
  simp[is_ArrayT_def] >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by
    metis_tac[literal_membership_straight, straight_fresh_cs_extends] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) (needle::xs)` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
      expr_sim_inv cenv cx env (ee with gas_obs := gs)` by simp[] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [SF ETA_ss]) >>
  drule_at (Pat `lower_word_args _ _ _ _ = _`)
    membership_lower_typed_args_sim_inv >>
  disch_then (drule_all o SRULE [MEM, SF ETA_ss]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def])
      >- suspend "normal" >> suspend "exit") >>
  suspend "exempt"
QED

Resume literal_expr_sim_ptr[normal]:
  qpat_x_assum `(\rr ee G tn t. _) _ _ _ _ _`
    (strip_assume_tac o BETA_RULE) >> gnvs[] >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  qpat_assum `!tail. eval_exprs _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!e. MEM e (e1::elems) ==> MEM e (e1::elems)` by simp[] >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all literal_eval_exprs_typed >> strip_tac >>
  Cases_on `vs` >- gvs[typed_args_post_ptr_def, typed_args_post_def] >>
  gnvs[typed_args_post_ptr_def, typed_args_post_def] >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  rename1 `value_has_type tv v` >>
  `EVERY (\e. THE (evaluate_type (get_tenv cx) (expr_type e)) = tv) elems` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `LIST_REL (\x v. eval_operand x t = SOME (typed_val_to_w256 tv v)) xs t'` by
    (irule literal_uniform_zip >>
     qexistsl [`elems`, `\e. THE (evaluate_type (get_tenv cx) (expr_type e))`] >>
     simp[]) >>
  `EVERY (\x. op_prov G x = NONE /\ op_taint tn x = {}) xs` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (metis_tac[not_fresh_at_mono]) >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) (needle::xs)` by simp[] >>
  `stmt_state_rel ctx fn cenv cx (es_end with gas_obs := []) t` by simp[] >>
  `~expr_has_effect (Builtin (BaseT BoolT) (Bop bop)
      [e1; Builtin (ArrayT (expr_type e1) n) (MakeArray (SOME (expr_type e1)) n) elems]) ==>
   pure_frame cenv fn es sa s0 t` by
    (rewrite_tac[loweringPostsTheory.expr_has_effect_thm, listTheory.EXISTS_DEF,
                 DE_MORGAN_THM] >>
     strip_tac >> qpat_x_assum `_ ==> pure_frame _ _ _ _ _ t` irule >>
     qpat_x_assum `~EXISTS _ elems`
       (assume_tac o REWRITE_RULE [listTheory.NOT_EXISTS]) >> simp[]) >>
  drule_all literal_typed_continuation_summary_ptr >> disch_tac >>
  qexists_tac `marks ++ []` >> disj1_tac >>
  asm_rewrite_tac[] >> irule gas_summary_ptr_at_bind_normal >>
  qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v::t'`] >>
  reverse conj_tac
  >- simp[gas_marked_exec_ptr_def] >>
  simp[] >> irule gas_summary_ptr_at_conseq >>
  first_assum (irule_at (Pos last)) >>
  simp[expr_type_def, is_word_type_def] >>
  rpt gen_tac >> disch_then (qx_choose_then `ww` strip_assume_tac) >>
  qexists_tac `ww` >> asm_rewrite_tac[]
QED
Resume literal_expr_sim_ptr[exit]:
  gnvs[] >> Cases_on `res` >- gvs[wb_args_exit_def] >>
  gnvs[wb_args_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  irule gas_summary_ptr_at_bind_exception >>
  goal_assum (drule_at (Pat `exit_result _`)) >>
  simp[gas_marked_exec_ptr_def] >> metis_tac[]
QED
Resume literal_expr_sim_ptr[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  asm_rewrite_tac[] >>
  gvs[ignore_bind_def, vyperStateTheory.bind_assoc, vyperStateTheory.bind_return] >>
  metis_tac[]
QED
Finalise literal_expr_sim_ptr

Theorem body_bop_in_literal_ptr_ok:
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  body_exprs_ptr_ok cx (e1::elems) ==>
  body_expr_ptr_ok cx
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray aet n) elems])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_ptr d ctx PG func cenv cx ty
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray aet n) elems]) es` by
    metis_tac[literal_expr_sim_ptr] >>
  conj_tac >- simp[] >>
  irule exprPtrUnwrapTheory.expr_vv_sim_ptr_stack >> simp[] >>
  reverse conj_tac >- metis_tac[eval_expr_builtin_value] >>
  drule_all literal_body_typing >> strip_tac >>
  `is_ArrayT a` by simp[is_ArrayT_def] >>
  metis_tac[exprSimBopInLiteralWordTheory.literal_compile_stack]
QED
