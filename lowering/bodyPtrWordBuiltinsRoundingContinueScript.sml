(* Lift the same-run rounding certificate to an expression continuation. *)
Theory bodyPtrWordBuiltinsRoundingContinue
Ancestors bodyPtrWordBuiltinsRoundingCases bodyPtrWordBuiltinsTypedShapes
  bodyPtrWordBuiltinsNotCompose exprSimUnopProps exprSimUnopComposeProps
  bodyPtrDefs exprSimDefs exprSimHypsDefs exprSimSource loweringPosts
  gasSummaryComposePtr vyperAST vyperValue valueEncoding compileEnv
  vyperTypeSystem vyperTyping integer_word words ptrDiscipline exprSimWordArgs
  stmtFragPtr vyperState

Theorem word_round_expr_outcome:
  ann = BaseT (IntT 256) /\ expr_type e = BaseT DecimalT /\
  value_has_type (BaseTV DecimalT) v /\
  (if up then compile_ceil else compile_floor) x 10000000000 s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 (BaseTV DecimalT) v) /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ fn_has_code s1 sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s1 /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = s1.cs_current_bb /\ t0.vs_inst_idx = LENGTH s1.cs_current_insts /\
  sa.cs_next_var <= s1.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ptr_val_ok cx (expr_type e) v x G tn t0 /\
  ee.gas_obs = [] /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (unop_result cx ann (if up then Ceil else Floor) [BaseT DecimalT] v vs,vs))
    (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann (if up then Ceil else Floor) [e])
        es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def] >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  `stmt_state_rel ctx func cenv cx ee t0` by gvs[expr_post_def] >>
  `eval_operand x t0 = SOME (i2w i)` by
    gvs[typed_val_to_w256_def, val_to_w256_def] >>
  drule_all word_round_typed_outcome >>
  strip_tac >> fs[builtin_result_def] >> rewrite_tac[unop_result_def] >>
  irule gas_outcome_ptr_conseq >> first_assum (irule_at Any) >>
  qexists_tac `\res fin gt r. expr_exit res r` >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[ghost_inv_gas_obs, ptr_val_ok_def, is_word_type_def] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  asm_rewrite_tac[] >> irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- (simp[expr_val_rel_def, evaluate_type_def, is_word_type_def,
           typed_val_to_w256_def, val_to_w256_def]) >>
  qexistsl_tac [`s1`, `t0`, `DecimalV i`, `x`] >> simp[]
QED
