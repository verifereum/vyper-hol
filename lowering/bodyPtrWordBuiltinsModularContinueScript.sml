(* Expression-post assembly at the same modular suffix endpoint. *)
Theory bodyPtrWordBuiltinsModularContinue
Ancestors bodyPtrWordBuiltinsModularCases bodyPtrWordBuiltinsRoundingContinue
  exprSimWordArgs exprSimWordBuiltins exprSimPrecompiles typedWordArgsPostPtr
  bodyPtrDefs loweringPosts exprSimSource gasSummaryComposePtr stmtFragPtr
  vyperAST vyperValue vyperTyping valueEncoding integer_word words compileEnv
  ptrDiscipline loweringSlice

Theorem word_pow_expr_outcome:
  ann = BaseT (UintT 256) /\ compile_pow_mod256 a b sm = (op,sb) /\
  value_has_type (BaseTV (UintT 256)) v1 /\ value_has_type (BaseTV (UintT 256)) v2 /\
  wb_args_post ctx func cenv cx es sa s0 ee [a;b] [v1;v2] t0 /\
  (!z. a = Var z ==> not_fresh_at sm z) /\ (!z. b = Var z ==> not_fresh_at sm z) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = sm.cs_current_bb /\ t0.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (builtin_result cx vs.accounts ann PowMod256 ts [v1;v2],vs))
    (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann PowMod256 args)
        es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t0 /\
   eval_operand a t0 = SOME (val_to_w256 v1) /\
   eval_operand b t0 = SOME (val_to_w256 v2)` by gvs[wb_args_post_def] >>
  drule_all word_pow_typed_outcome >> strip_tac >>
  irule gas_outcome_ptr_conseq >> first_assum (irule_at Any) >>
  qexists_tac `\res fin gt r. expr_exit res r` >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[ghost_inv_gas_obs, ptr_val_ok_def, is_word_type_def] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> irule expr_post_word_builtin >>
  simp[is_word_type_def, word_value_def, val_to_w256_def] >>
  qexistsl_tac [`sm`, `t0`, `[v1;v2]`, `[a;b]`] >> simp[]
QED

Theorem word_modular_expr_outcome:
  ann = BaseT (UintT 256) /\
  (if is_mul then compile_mulmod else compile_addmod) a b c sm = (op,sb) /\
  value_has_type (BaseTV (UintT 256)) v1 /\ value_has_type (BaseTV (UintT 256)) v2 /\
  value_has_type (BaseTV (UintT 256)) v3 /\
  wb_args_post ctx func cenv cx es sa s0 ee [a;b;c] [v1;v2;v3] t0 /\
  (!z. a = Var z ==> not_fresh_at sm z) /\ (!z. b = Var z ==> not_fresh_at sm z) /\
  (!z. c = Var z ==> not_fresh_at sm z) /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ op_taint tn c = {} /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ~ctx_has_dalloca ctx /\ ~t0.vs_halted /\
  t0.vs_current_bb = sm.cs_current_bb /\ t0.vs_inst_idx = LENGTH sm.cs_current_insts /\
  sa.cs_next_var <= sm.cs_next_var /\ ghost_inv d cenv cx ee G tn t0 /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (builtin_result cx vs.accounts ann (if is_mul then MulMod else AddMod) ts [v1;v2;v3],vs))
    (ee,t0,G,tn)
    (\res fin G' tn' u. ?v'. res = INL v' /\
      expr_post ctx func cenv cx (Builtin ann (if is_mul then MulMod else AddMod) args)
        es sa sb s0 fin v' op u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v' op G' tn' u /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn')
    (\res fin gt r. expr_exit res r)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee t0 /\
   eval_operand a t0 = SOME (val_to_w256 v1) /\
   eval_operand b t0 = SOME (val_to_w256 v2) /\
   eval_operand c t0 = SOME (val_to_w256 v3)` by gvs[wb_args_post_def] >>
  Cases_on `val_to_w256 v3 = 0w`
  >- (drule_all word_modular_typed_abort_outcome >> strip_tac >> first_assum irule) >>
  drule_all word_modular_typed_outcome >> strip_tac >>
  irule gas_outcome_ptr_conseq >> first_assum (irule_at Any) >>
  qexists_tac `\res fin gt r. expr_exit res r` >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[ghost_inv_gas_obs, ptr_val_ok_def, is_word_type_def] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> irule expr_post_word_builtin >>
  simp[is_word_type_def, word_value_def, val_to_w256_def] >>
  qexistsl_tac [`sm`, `t0`, `[v1;v2;v3]`, `[a;b;c]`] >> simp[]
QED

Theorem word_uint_args_post:
  EVERY (\e. expr_type e = BaseT (UintT 256)) args /\
  typed_args_post ctx func cenv cx es sa s0 ee args xs vs t ==>
  wb_args_post ctx func cenv cx es sa s0 ee xs vs t
Proof
  simp[typed_args_post_def, wb_args_post_def] >> strip_tac >> simp[] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  qpat_x_assum `LENGTH _ = _` mp_tac >>
  map_every qid_spec_tac [`vs`, `xs`, `args`] >>
  Induct >> Cases_on `xs` >> Cases_on `vs` >>
  simp[] >> rpt strip_tac >>
  gvs[evaluate_type_def] >>
  `!v. typed_val_to_w256 (BaseTV (UintT 256)) v = val_to_w256 v` by
    (Cases >> simp[typed_val_to_w256_def]) >> metis_tac[]
QED
