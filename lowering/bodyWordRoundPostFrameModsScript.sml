(* The linked post at the fresh-vars endpoint of a decimal rounding suffix. *)
Theory bodyWordRoundPostFrameMods
Ancestors
  bodyForRangeScalarFrameMods bodyFullPostsMods bodyFullUnwrapRun
  exprSimUnopProps exprSimWordArgs exprSimProps allocasBelowFmpUpdatesProps
  loweringShapeDefs loweringStateRelDefs exprLoweringProps exprSimMemDefs
  loweringPosts bodyPtrDefs ptrDiscipline valueEncoding vyperValue
  compileEnv vyperAST venomState pred_set finite_map

Theorem rounding_vars_state_rel[local]:
  stmt_state_rel H ctx func cenv cx mid t /\
  local_ptrs_reserved cenv s1 /\
  (!x. not_fresh_at s1 x ==>
       lookup_var x (t with vs_vars := vars) = lookup_var x t) ==>
  stmt_state_rel H ctx func cenv cx mid
    ((t with vs_vars := vars) with vs_inst_idx := k)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_vars_frame >> simp[] >>
  fs[local_ptrs_reserved_def] >> rpt strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem word_rounding_post_frame_mods:
  (bt = Ceil \/ bt = Floor) /\ expr_type e = BaseT DecimalT /\
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
  expr_store_bound cx (post_value_type cenv e) v x t /\
  t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ptr_val_ok cx (post_value_type cenv e) v x G1 tn1 t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G1 t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  sa.cs_next_var <= s1.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!n sz. cenv.ce_return_buf = SOME (PtrVar (Var n) sz) ==> not_fresh_at sa n) /\
  (!n sz. cenv.ce_return_pc = SOME (PtrVar (Var n) sz) ==> not_fresh_at sa n) /\
  u = (t with vs_vars := u.vs_vars) /\ z = (u with vs_inst_idx := k) /\
  eval_operand op z = SOME (typed_val_to_w256 (BaseTV (IntT 256)) v') /\
  (!n. not_fresh_at s1 n ==>
       lookup_var n z = lookup_var n t /\ FLOOKUP G' n = FLOOKUP G1 n /\
       op_taint tn' (Var n) = op_taint tn1 (Var n)) /\
  tn'.t_mem = tn1.t_mem /\ tn'.t_stor = tn1.t_stor /\
  tn'.t_trans = tn1.t_trans /\ tn'.t_imm = tn1.t_imm /\
  op_taint tn' op = {} /\ op_prov G' op = NONE /\
  alloca_history func z /\ z.vs_current_bb = sb.cs_current_bb /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  expr_post_mods H ctx func cenv cx (Builtin (BaseT (IntT 256)) bt [e])
    es sa sb s0 mid v' op z /\
  expr_store_bound cx (BaseT (IntT 256)) v' op z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
  s0.vs_alloca_next <= z.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' z /\
  ptr_val_ok cx (BaseT (IntT 256)) v' op G' tn' z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `!n. not_fresh_at sa n ==> not_fresh_at s1 n` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `z.vs_memory = t.vs_memory /\ z.vs_data_section = t.vs_data_section /\
   z.vs_allocas = t.vs_allocas /\ z.vs_alloca_next = t.vs_alloca_next /\
   z.vs_call_ctx = t.vs_call_ctx /\ z.vs_accounts = t.vs_accounts /\
   z.vs_transient = t.vs_transient /\ z.vs_immutables = t.vs_immutables /\
   (allocas_below_fmp z <=> allocas_below_fmp t)` by
    (qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     simp[allocas_below_fmp_updates]) >>
  `stmt_state_rel H ctx func cenv cx mid z` by
    (qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `u = _` (fn th => once_rewrite_tac[th]) >>
     irule rounding_vars_state_rel >>
     reverse conj_tac >- (irule expr_post_state >> metis_tac[]) >>
     qexists_tac `s1` >> simp[] >>
     qpat_assum `!n. not_fresh_at s1 n ==> lookup_var n z = _ /\ _` mp_tac >>
     qpat_assum `z = _` (fn th => once_rewrite_tac[th]) >> simp[lookup_var_def]) >>
  qpat_x_assum `z = _` kall_tac >> qpat_x_assum `u = _` kall_tac >>
  simp[is_word_type_def, ptr_val_ok_def, expr_store_bound_word] >>
  conj_tac
  >- (simp[expr_post_mods_def] >> conj_tac
      >- (irule expr_post_unop >>
          simp[expr_val_rel_def, evaluate_type_def, is_word_type_def] >>
          qexistsl_tac [`s1`, `t`, `v`, `x`] >> simp[]) >>
      irule immutable_frame_mods_exterior_frame >>
      qexistsl_tac [`mid`, `t`, `s1`] >> simp[]) >>
  conj_tac
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl_tac [`G1`, `mid`, `t`, `s1`, `tn1`] >> simp[] >> metis_tac[]) >>
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G1`, `tn1`] >>
  simp[] >> metis_tac[]
QED
