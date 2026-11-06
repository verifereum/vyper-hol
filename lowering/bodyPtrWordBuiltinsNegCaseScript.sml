(* Typed Neg boundaries retain the original scalar operand judgment. *)
Theory bodyPtrWordBuiltinsNegCase
Ancestors
  bodyPtrWordBuiltinsNegPost bodyPtrWordBuiltinsNotCase
  exprSimSource exprSimHypsDefs vyperTyping vyperTypeSystem
  exprSimUnopProps exprSimUnopComposeProps exprUnopStraight
  fragGasFresh freshWrites exprSimDefs loweringPosts exprLoweringProps
  vyperAST vyperInterpreter varsExt compileEnv

Theorem word_neg_operand_pre:
  expr_body_pre cenv cx env (Builtin ann Neg [e]) es ==>
  ann = expr_type e /\
  is_numeric_type (expr_type e) /\ ~is_uint_type (expr_type e) /\
  expr_body_pre cenv cx env e es
Proof
  strip_tac >>
  `ann = expr_type e /\ is_numeric_type (expr_type e) /\
   ~is_uint_type (expr_type e)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  simp[] >> drule expr_body_pre_builtin_arg >>
  disch_then irule >> gvs[expr_body_pre_def]
QED

Theorem word_neg_typed_post:
  is_numeric_type ann /\ ~is_uint_type ann /\ ann = expr_type e /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  compile_neg x ann s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 tv v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\
  fn_has_code s1 sb func /\ local_ptrs_reserved cenv s1 /\
  ~t0.vs_halted /\ t0.vs_current_bb = s1.cs_current_bb /\
  t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\
  w2i (FST (type_bounds ann)) < w2i (typed_val_to_w256 tv v) ==>
  ?v' t. unop_result cx ann Neg [expr_type e] v ee = INL v' /\
    run_inst_seq (emitted_insts s1 sb) t0 = OK t /\
    expr_post ctx func cenv cx (Builtin ann Neg [e]) es sa sb s0 ee v' op
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `is_word_type ann` by
    (qpat_x_assum `is_numeric_type ann` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `ann` >> simp[is_numeric_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> simp[is_word_type_def]) >>
  `stmt_state_rel ctx func cenv cx ee t0` by gvs[expr_post_def] >>
  `straight_fresh (compile_neg x ann)` by metis_tac[straight_fresh_neg, ETA_AX] >>
  drule_all neg_typed_source >> disch_then (qspec_then `ee` mp_tac) >>
  simp[] >> strip_tac >>
  `fresh_vars_wrt s1 (drop_fresh s1 t0)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand x (drop_fresh s1 t0) = SOME (typed_val_to_w256 tv v)` by
    simp[eval_operand_drop_fresh] >>
  drule_all compile_neg_run >> simp[] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  rename1 `run_inst_seq _ t0 = OK actual` >>
  qexists `actual` >> simp[] >>
  irule expr_post_unop >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (simp[expr_val_rel_def] >> rpt strip_tac >> gvs[]) >>
  qexistsl [`s1`, `t0`, `v`, `x`] >> gvs[]
QED
