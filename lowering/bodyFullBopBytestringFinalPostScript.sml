Theory bodyFullBopBytestringFinalPost
Ancestors
  bodyFullBopBytestringPost bodyFullBopBytestringDigest bodyFullGhostFrame
  bodyPtrSignedConvertSourceFrame bodyFullUnwrapRun wordArgsPtr
  bodySimFull exprBopDigestProps bodyPtrDefs loweringStateRelDefs
  exprBopSimProps exprLoweringProps loweringPosts exprSimMemDefs compileEnv vyperAST

Theorem bop_bytestring_final_post:
  wb_frame cenv es es1 sa s0 t /\
  (~expr_has_effect e1 ==> pure_frame cenv func es sa s0 t) /\
  wb_frame cenv es1 ee s1 t u /\
  (~expr_has_effect e2 ==> pure_frame cenv func es1 s1 t u) /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  stmt_state_rel H ctx func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv s2 /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at s2 x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at s2 x) /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\
  is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq) /\
  ghost_inv_at D lo d cenv cx ee G2 tn2 u /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 s1 G1 tn1 t G2 tn2 /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ t.vs_alloca_next <= u.vs_alloca_next /\
  alloca_history func u /\ fn_inst_ids_distinct func /\
  fn_has_code s2 sb func /\
  (if bop = Eq then emit_op EQ [h1;h2] s2
   else emit_op ISZERO [FST (emit_op EQ [h1;h2] s2)] (SND (emit_op EQ [h1;h2] s2))) = (op,sb) /\
  u.vs_current_bb = s2.cs_current_bb /\ u.vs_inst_idx = LENGTH s2.cs_current_insts /\
  run_inst_seq (emitted_insts s2 sb) u = OK raw0 /\
  (raw0 with vs_vars := u.vs_vars) = u /\
  ss = (raw with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (raw with vs_vars := u.vs_vars) = u /\
  ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand op ss = SOME (bool_to_word b) /\
  (!z. not_fresh_at s2 z ==> lookup_var z ss = lookup_var z u /\
    FLOOKUP Gf z = FLOOKUP G2 z /\ FLOOKUP tnf.t_var z = FLOOKUP tn2.t_var z) /\
  tnf.t_mem = tn2.t_mem /\ tnf.t_stor = tn2.t_stor /\
  tnf.t_trans = tn2.t_trans /\ tnf.t_imm = tn2.t_imm /\
  op_prov Gf op = NONE /\ op_taint tnf op = {} ==>
  expr_post H ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
    es sa sb s0 ee (BoolV b) op ss /\
  expr_store_bound cx (expr_type (Builtin (BaseT BoolT) (Bop bop) [e1;e2])) (BoolV b) op ss /\
  ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func ss /\ s0.vs_alloca_next <= ss.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee Gf tnf ss /\
  ptr_val_ok cx (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2]))
    (BoolV b) op Gf tnf ss /\
  (~is_word_type (post_value_type cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2])) ==>
    ptr_buf_ok cenv (Builtin (BaseT BoolT) (Bop bop) [e1;e2]) op Gf ss) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `ss = u with <|vs_vars := ss.vs_vars; vs_inst_idx := ss.vs_inst_idx|>` by
    (qpat_x_assum `raw with vs_vars := _ = _` mp_tac >>
     qpat_x_assum `ss = _` SUBST1_TAC >>
     simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ee ss` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl_tac [`u`, `s2`] >>
     simp[] >> metis_tac[]) >>
  `ss.vs_memory = u.vs_memory /\ ss.vs_allocas = u.vs_allocas /\
   ss.vs_alloca_next = u.vs_alloca_next /\ ss.vs_call_ctx = u.vs_call_ctx /\
   ss.vs_accounts = u.vs_accounts /\ ss.vs_transient = u.vs_transient /\
   ss.vs_immutables = u.vs_immutables` by
    (qpat_assum `ss = u with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  `ghost_inv_at D lo d cenv cx ee Gf tnf ss` by
    (irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G2`, `ee`, `u`, `s2`, `tn2`] >>
     simp[ptrDisciplineTheory.op_taint_def]) >>
  `expr_post H ctx func cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
     es sa sb s0 ee (BoolV b) op ss` by
    (irule bop_bytestring_frames_post >> simp[] >>
     qexistsl_tac [`es1`, `s1`, `s2`, `t`, `u`] >> simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (`ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
      ghost_kept cenv es1 s1 G1 tn1 t G2 tn2` by
       (fs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
     drule_all wordArgsPtrTheory.ghost_kept_wb_trans >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (fs[ghost_kept_def, ghost_kept_at_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_at_clean_suffix >> qexistsl_tac [`G2`, `tn2`] >>
     simp[ptrDisciplineTheory.op_taint_def] >> rpt strip_tac >>
     `not_fresh_at s2 x` by
       (metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >> metis_tac[]) >>
  `alloca_history func (raw0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule emitted_alloca_history >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts s2 sb`, `u`, `s2`] >> simp[] >>
     drule (SRULE [LET_THM, pairTheory.UNCURRY] comparison_digest_shape) >> strip_tac >>
     simp[] >> conj_tac >- fs[stmt_state_rel_def] >>
     fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `sb.cs_current_bb = s2.cs_current_bb` by
    (drule (SRULE [LET_THM, pairTheory.UNCURRY] comparison_digest_shape) >> simp[]) >>
  `alloca_history func ss` by
    (irule allocaHistoryTheory.alloca_history_frame >>
     qexists_tac `raw0 with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
     qpat_assum `raw0 with vs_vars := _ = _` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  simp[post_value_type_def, expr_type_def, is_word_type_def,
       expr_store_bound_def, ptr_val_ok_def]
QED
