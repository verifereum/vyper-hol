(* Same-run unsigned scaling lifted to the expression continuation. *)
Theory bodyPtrWordBuiltinsScalingContinue
Ancestors bodyPtrWordBuiltinsScalingCases bodyPtrWordBuiltinsRoundingContinue
  exprSimUnopProps exprSimUnopComposeProps exprSimWordBuiltins
  bodyPtrDefs exprSimDefs loweringPosts gasSummaryComposePtr
  vyperAST vyperValue vyperTyping valueEncoding integer_word words
  ptrDiscipline compileEnv vyperState exprSimSource stmtFragPtr vyperTypeSystem exprSimWordArgs

Theorem word_scale_expr_outcome:
  ann = BaseT (UintT 256) /\ expr_type e = BaseT (UintT k) /\ k <= 256 /\
  value_has_type (BaseTV (UintT k)) v /\
  compile_as_wei_value_int x (denomination_multiplier dn) F s1 = (op,sb) /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v x t0 /\
  eval_operand x t0 = SOME (typed_val_to_w256 (BaseTV (UintT k)) v) /\
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
    (\vs. (unop_result cx ann (AsWeiValue dn) [BaseT (UintT k)] v vs,vs))
    (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann (AsWeiValue dn) [e])
        es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `v = IntV (&w2n (val_to_w256 v))` by metis_tac[uint_value_word_rep] >>
  qabbrev_tac `w = val_to_w256 v` >>
  `op_prov G x = NONE /\ op_taint tn x = {}` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  `stmt_state_rel ctx func cenv cx ee t0` by gvs[expr_post_def] >>
  `eval_operand x t0 = SOME w` by gvs[typed_val_to_w256_def] >>
  Cases_on `w2n w * denomination_multiplier dn < dimword (:256)`
  >- (drule_all word_scale_typed_normal_outcome >>
      strip_tac >> fs[builtin_result_def] >> rewrite_tac[unop_result_def] >>
      irule gas_outcome_ptr_conseq >> first_assum (irule_at Any) >>
      qexists_tac `\res fin gt r. expr_exit res r` >> simp[] >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      simp[ghost_inv_gas_obs, ptr_val_ok_def, is_word_type_def] >>
      `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
      pop_assum SUBST1_TAC >> irule expr_post_unop >> simp[is_word_type_def] >>
      conj_tac
      >- (simp[expr_val_rel_def, evaluate_type_def, is_word_type_def,
                typed_val_to_w256_def, val_to_w256_def] >>
          simp[integer_wordTheory.i2w_def, GSYM word_mul_n2w, WORD_MULT_COMM]) >>
      qexistsl_tac [`s1`, `t0`, `IntV (&w2n w)`, `x`] >> simp[]) >>
  drule_all word_scale_typed_abort_outcome >> strip_tac >>
  fs[builtin_result_def] >> rewrite_tac[unop_result_def] >>
  asm_rewrite_tac[] >> first_assum irule
QED
