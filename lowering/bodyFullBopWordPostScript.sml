Theory bodyFullBopWordPost
Ancestors
  bodyBinopFragMemory
  bodyFullGhostFrame bodyPtrBopScalarOutcome exprBopSimProps exprSimProps
  bodySimFull bodyFullBopWordLayout wordArgsPtr exprSimWordArgs exprSimSource exprSimOperators
  loweringPosts exprLoweringProps freshWrites compileEnv ptrDiscipline
  venomState vyperState finite_map pred_set allocaHistory valueEncoding loweringStateRelDefs ghostPcTransportPtr
  augAssignPtrCompiler vyperTypeSystem bodyFullUnwrapRun

Theorem bop_word_suffix_success_post:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 sb /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= sb.cs_next_var /\
  (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l) /\
  cs_extends shadow_sa shadow_s1 /\ cs_extends shadow_s1 shadow_s2 /\
  cs_extends shadow_s2 shadow_sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\ fn_has_code shadow_s2 shadow_sb shadow_func /\
  local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  (expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
      expr_store_bound cx (expr_type e1) v1 x t /\
      t.vs_current_bb = s1.cs_current_bb /\ t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
      (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted /\ mid.gas_obs = []) /\
  (expr_post H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
      expr_store_bound cx (expr_type e2) v2 y u /\
      u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx fin G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
      (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 u) /\
      ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ ~u.vs_halted /\ fin.gas_obs = []) /\
  is_word_type ann /\ MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
    (emitted_insts s2 sb) B /\
  run_inst_seq (emitted_insts s2 sb) u = OK r /\
  eval_operand op r = SOME (val_to_w256 v) /\ word_value v /\
  bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
  op_prov G' op = NONE /\ op_taint tn' op = {} /\
  tn'.t_mem = tn2.t_mem /\ tn'.t_stor = tn2.t_stor /\
  tn'.t_trans = tn2.t_trans /\ tn'.t_imm = tn2.t_imm /\
  (!z. not_fresh_at s2 z ==> FLOOKUP G' z = FLOOKUP G2 z /\
    FLOOKUP tn'.t_var z = FLOOKUP tn2.t_var z) ==>
  (expr_post H ctx func cenv cx (Builtin ann (Bop bop) [e1;e2]) es sa sb s0 (fin with gas_obs := []) v op (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)) /\
    expr_store_bound cx (expr_type (Builtin ann (Bop bop) [e1;e2])) v op (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)) /\
    (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)).vs_current_bb = sb.cs_current_bb /\ (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)).vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)) /\ s0.vs_alloca_next <= (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)).vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx (fin with gas_obs := []) G' tn' (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)) /\
    ptr_val_ok cx (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) v op G' tn' (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)) /\
    (~is_word_type (post_value_type cenv (Builtin ann (Bop bop) [e1;e2])) ==>
      ptr_buf_ok cenv (Builtin ann (Bop bop) [e1;e2]) op G' (r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb))) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn')
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >> gvs[] >>
  drule_all bop_scalar_seq_runtime_frame >> strip_tac >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel H ctx func cenv cx fin (u with vs_vars := r.vs_vars)` by
    (irule stmt_state_rel_vars_frame >>
     simp[expr_post_state] >>
     gvs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[expr_post_state]) >>
  `fin with gas_obs := [] = fin` by
    simp[evaluation_state_component_equality] >>
  `sa.cs_next_id <= s1.cs_next_id` by
    (drule expr_body_pre_bop >> strip_tac >>
     metis_tac[expr_body_pre_lower_value_word_shape, word_value_type_word]) >>
  simp[] >> conj_tac
  >- (irule expr_post_bop >>
      simp[] >>
      reverse conj_tac
      >- (goal_assum (drule_at Any) >>
          goal_assum (drule_at Any) >>
          gvs[lookup_var_def] >>
          goal_assum (drule_at Any) >>
          qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
      simp[stmt_state_rel_inst_idx]) >>
  `MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
    UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt; GtE;
    Exp; Min; Max; In; NotIn]` by
    (drule expr_body_pre_bop >> strip_tac >>
     qpat_x_assum `well_typed_binop _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bop` >>
     simp[well_typed_binop_def]) >>
  drule compile_binop_straight_fresh_ptr >>
  simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
  simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.expr_store_bound_word,
       bodyPtrDefsTheory.ptr_val_ok_word] >>
  conj_tac
  >- (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (drule bodyPtrBopScalarSeqTheory.bop_scalar_seq_opcodes >> strip_tac >>
      qpat_assum `u.vs_inst_idx = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
      irule bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
      conj_tac >- (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      conj_tac >- (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
      reverse conj_tac
      >- (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
          drule_all bop_scalar_seq_outputs >> simp[]) >>
      qpat_x_assum `fn_has_code s2 sb func` mp_tac >>
      simp[fragExecTheory.fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >>
      strip_tac >> goal_assum (drule_at Any) >> simp[listTheory.DROP_APPEND]) >>
  conj_tac
  >- (qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G2`,`fin`,`u`,`s2`,`tn2`] >>
      simp[lookup_var_def, op_taint_def] >>
      qpat_x_assum `r = _` (fn th => once_rewrite_tac[th]) >>
      simp[lookup_var_def] >> conj_tac >> rpt strip_tac >>
      rename1 `not_fresh_at s2 z` >>
      `not_fresh_at sa z` by metis_tac[] >>
      irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (`wb_frame cenv es mid sa s0 t` by metis_tac[expr_post_frame] >>
     `MAP FDOM es.scopes = MAP FDOM mid.scopes` by metis_tac[] >>
     drule_all ghost_kept_at_wb_trans >> strip_tac >> simp[]) >>
  irule ghost_kept_at_clean_suffix >>
  goal_assum (drule_at Any) >> simp[op_taint_def] >>
  rpt strip_tac >>
  `not_fresh_at s2 x'` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  simp[]
QED
