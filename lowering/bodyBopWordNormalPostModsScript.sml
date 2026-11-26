(* Normal linked post at the end of the successful word Bop suffix. *)
Theory bodyBopWordNormalPostMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullUnwrapRun bodyBinopFragMemory
  bodyPtrBopScalarOutcome exprBopSimProps exprSimProps wordArgsPtr exprSimWordArgs
  augAssignPtrCompiler allocasBelowFmpUpdatesProps instIdxIndep
  freshWrites fragExec rich_list list exprSimMemDefs vyperTypeSystem
  bodyFullPostsMods exprLoweringProps venomState ptrDiscipline loweringPosts
  vyperAST vyperState bodyPtrDefs loweringStateRelDefs

Theorem bop_word_suffix_cursor[local]:
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  fn_has_code s2 sb func /\
  u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
  alloca_history func u /\
  bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
    (emitted_insts s2 sb) B /\
  r = (u with vs_vars := r.vs_vars) ==>
  let t' = r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb) in
  t'.vs_current_bb = sb.cs_current_bb /\
  t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t'
Proof
  simp[LET_THM] >> strip_tac >>
  `MEM bop [Add; Sub; Mul; Div; Mod; UnsafeAdd; UnsafeSub; UnsafeMul;
    UnsafeDiv; And; Or; XOr; ShL; ShR; Eq; NotEq; Lt; LtE; Gt; GtE;
    Exp; Min; Max; In; NotIn]` by
    (qpat_assum `well_typed_binop _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bop` >> simp[well_typed_binop_def]) >>
  drule compile_binop_straight_fresh_ptr >>
  simp[straight_fresh_def] >> disch_then drule >> strip_tac >>
  conj_tac
  >- (qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- simp[] >>
  qpat_assum `u.vs_inst_idx = _` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  irule alloca_history_no_alloca_slice >>
  qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  reverse conj_tac
  >- (simp[EVERY_MEM] >> rpt strip_tac >> drule_all bop_scalar_seq_outputs >> simp[]) >>
  qpat_x_assum `fn_has_code s2 sb func` mp_tac >>
  simp[fn_has_code_def, IS_PREFIX_APPEND] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[DROP_APPEND]
QED

Theorem bop_word_normal_post_mods:
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\ is_word_type ann /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op,sb) /\
  fn_has_code s2 sb func /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  expr_post_mods H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  expr_post_mods H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
  u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
  alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx fin G2 tn2 u /\
  ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\ fin.gas_obs = [] /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\ MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  bop_scalar_seq {z | not_fresh_at s2 z} ({x;y} UNION IMAGE Lit UNIV)
    (emitted_insts s2 sb) B /\
  run_inst_seq (emitted_insts s2 sb) u = OK r /\
  bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 fin = INL v /\
  expr_val_rel cx ann v op r /\ op_prov G' op = NONE /\ op_taint tn' op = {} /\
  tn'.t_mem = tn2.t_mem /\ tn'.t_stor = tn2.t_stor /\
  tn'.t_trans = tn2.t_trans /\ tn'.t_imm = tn2.t_imm /\
  (!z. not_fresh_at s2 z ==> FLOOKUP G' z = FLOOKUP G2 z /\
    FLOOKUP tn'.t_var z = FLOOKUP tn2.t_var z) ==>
  let e = Builtin ann (Bop bop) [e1;e2];
      ee = fin with gas_obs := [];
      t' = r with vs_inst_idx := u.vs_inst_idx + LENGTH (emitted_insts s2 sb)
  in
    expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t' /\
    expr_store_bound cx (post_value_type cenv e) v op t' /\
    t'.vs_current_bb = sb.cs_current_bb /\ t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t' /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
    s0.vs_alloca_next <= t'.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t' /\
    ptr_val_ok cx (post_value_type cenv e) v op G' tn' t' /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G' t') /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all bop_scalar_seq_runtime_frame >> simp[] >> strip_tac >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  drule_all bop_word_suffix_cursor >> simp[LET_THM] >> strip_tac >>
  fs[expr_post_mods_def] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >> decide_tac) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >> decide_tac) >>
  qmatch_goalsub_abbrev_tac `r with vs_inst_idx := idx` >>
  `!z. not_fresh_at s2 z ==> lookup_var z (r with vs_inst_idx := idx) = lookup_var z u` by
    (qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[lookup_var_def]) >>
  `!z. not_fresh_at s2 z ==> op_taint tn' (Var z) = op_taint tn2 (Var z)` by
    simp[op_taint_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp r)` by
    (qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >>
     simp[allocas_below_fmp_updates]) >>
  `s0.vs_alloca_next <= r.vs_alloca_next` by
    (qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[] >> decide_tac) >>
  simp[post_value_type_def, expr_type_def, expr_store_bound_word, ptr_val_ok_word] >>
  conj_tac >- (conj_tac >- suspend "ordinary" >> suspend "immutable") >>
  conj_tac >- suspend "ghost" >>
  suspend "kept"
QED

Resume bop_word_normal_post_mods[ordinary]:
  irule expr_post_bop_rel >> simp[] >> conj_tac
  >- (qpat_assum `expr_val_rel cx ann v op r` mp_tac >>
      simp[NoAsms, expr_val_rel_def, eval_op_inst_idx]) >>
  conj_tac
  >- (qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >>
      simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_vars_frame >>
      simp[expr_post_state] >> fs[local_ptrs_reserved_def, lookup_var_def] >>
      metis_tac[expr_post_state]) >>
  qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ t` (irule_at Any) >>
  qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ u` (irule_at Any) >>
  simp[lookup_var_def] >>
  qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Resume bop_word_normal_post_mods[immutable]:
  irule immutable_frame_mods_exterior_frame >>
  qpat_assum `immutable_frame_mods _ _ _ fin u` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv s2` (irule_at Any) >>
  simp[] >> qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Resume bop_word_normal_post_mods[ghost]:
  irule ghost_inv_at_mods_exterior_frame >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ fin G2 tn2 u` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv s2` (irule_at Any) >>
  simp[] >> qpat_assum `r = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Resume bop_word_normal_post_mods[kept]:
  `wb_frame cenv es mid sa s0 t` by
    (irule expr_post_frame >> goal_assum (drule_at Any)) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by simp[] >>
  drule_all ghost_kept_at_wb_trans >> strip_tac >>
  irule ghost_kept_at_clean_suffix >> goal_assum (drule_at Any) >> simp[]
QED

Finalise bop_word_normal_post_mods
