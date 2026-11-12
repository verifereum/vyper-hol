Theory exprSimIfExpWidenedRoot
Ancestors
  exprSimIfExpWidenedSelectedCounted exprSimIfExpWidenedSource
  exprSimIfExpWidenedPost exprSimIfExpWidenedCode
  exprSimDefs exprLoweringProps exprSimIfExp exprSimIfExpCompat
  exprSimUnwrap compileEnv loweringStateRelDefs gasContext fragExec stmtReasonVvMemory
  gasOutcome gasSummary fragGasMode fragGasPath fragGasSeqAbort
  vyperValue valueEncoding exprSimWordArgs stmtSimDefs localPtrsProps vyperState exprBopSimProps
  placeTypedCopyPath stmtSimProps emitHelperProps venomExecSemantics venomInst venomState exprSimUint2Str loweringPosts

Theorem outcome_zero_suffix[local]:
  gas_outcome F tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u /\ ~u.vs_halted ==>
    ?v. gas_marked_path F ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q' R
Proof
  rw[gas_outcome_def] >> qexists_tac `marks` >>
  Cases_on `gas_summary_at F (ctx,func) marks source (es,s0) Q R`
  >- (disj1_tac >>
      fs[gas_summary_at_def] >>
      gvs[]
      >- (`~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             metis_tac[cj 1 gas_path_normal]) >>
          first_x_assum drule_all >> strip_tac >>
          qexistsl_tac [`res`, `es_end`, `OK v`] >>
          simp[] >> fs[gas_marked_exec_def] >>
          metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem assign_join_path[local]:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ eval_operand op u = SOME w ==>
  gas_marked_path F ctx func u 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  strip_tac >>
  `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb u.vs_inst_idx = SOME (mk_inst sx.cs_next_id ASSIGN [op] [rv])` by
    metis_tac[place_copy_emit_instruction] >>
  drule_at (Pat `get_instruction _ _ = _`) gas_marked_path_step >>
  simp[] >>
  disch_then irule >> simp[is_terminator_def] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `update_var rv w u` >>
  conj_tac >- (irule u2s_step_assign >> simp[]) >>
  `sy.cs_current_insts = sx.cs_current_insts ++
      [mk_inst sx.cs_next_id ASSIGN [op] [rv]] /\
   sy.cs_current_bb = sx.cs_current_bb` by
    metis_tac[emit_inst_extends] >>
  `LENGTH sy.cs_current_insts = SUC (LENGTH sx.cs_current_insts)` by simp[] >>
  simp[gas_marked_path_def] >>
  irule emit_jump_zero_path >>
  conj_tac >- simp[update_var_def] >>
  qexistsl_tac [`sy`, `sz`] >>
  drule_all emit_inst_extends >> strip_tac >>
  drule_all emit_inst_extends >> strip_tac >>
  simp[update_var_def]
QED

Theorem normalized_arm_join_outcome[local]:
  (~expr_has_effect (IfExp ann c a b) ==> ~expr_has_effect (IfExp ann nc na nb)) /\
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func ce cx (IfExp ann nc na nb) es1 sc sd
        (jump_to lbl tt) ee v op u /\
      (~is_word_type ann ==> vv_at ce cx ann sc sd ee tv
        (LocatedValue ann (mk_ptr op LocMemory)) u) /\
      u.vs_current_bb = sd.cs_current_bb /\
      u.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee r. expr_exit res r) /\
  emit_inst ASSIGN [op] [rv] sd = ((),se) /\
  emit_inst JMP [Label xl] [] se = ((),sf) /\
  fn_has_code sd se func /\ fn_has_code se sf func /\
  sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  expr_post ctx func ce cx c es sa s1 s0 es1 cv cop tt /\
  (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id ==>
  gas_outcome F tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func ce cx (IfExp ann c a b) es sa sb s0 ee tv
        (if is_word_type ann then StackValue ann (Var rv)
         else LocatedValue ann (mk_ptr (Var rv) LocMemory)) u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = 0)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> irule outcome_zero_suffix >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  `?w. eval_operand op u = SOME w` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all assign_join_path >> disch_then assume_tac >>
  qexists_tac `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH se.cs_current_insts)` >>
  conj_tac >- metis_tac[] >>
  qexists_tac `tv` >> simp[] >>
  reverse conj_tac >- simp[jump_to_def] >>
  irule normalized_ifexp_root_vv_post >> metis_tac[]
QED

Theorem widened_ifexp_vv_sim:
  expr_type c = BaseT BoolT /\ expr_type a = ann /\ expr_type b = ann /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
    type_memory_bytes ce ann = type_memory_size tv /\
    type_memory_size tv < dimword (:256)) /\
  expr_sim ctx func ce cx (BaseT BoolT) c es /\
  (!gs v ee. vyperState$bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee) ==>
    !e. (e = a \/ e = b) ==>
      expr_body_pre ce cx env e ee /\ expr_vv_sim ctx func ce cx ty e ee) ==>
  expr_vv_sim ctx func ce cx ty (IfExp ann c a b) es
Proof
  strip_tac >> rw[expr_vv_sim_def] >>
  `!sa sb op. lower_value compile_expr ce (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  `!e sa sb op. (e = a \/ e = b) /\
    lower_value compile_expr ce ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  drule_all compile_expr_ifexp_states >> strip_tac >>
  imp_res_tac compile_expr_extends >>
  imp_res_tac cs_extends_emit_inst >>
  imp_res_tac cs_extends_new_block >>
  `ci_mono s7a s8` by
    metis_tac[ci_mono_compile_ifexp_arm, pairTheory.SND] >>
  `ci_mono s11a s12` by
    metis_tac[ci_mono_compile_ifexp_arm, pairTheory.SND] >>
  fs[ci_mono_def] >>
  `cs_extends s7a sb /\ cs_extends s11a sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s7 s7a func /\ fn_has_code s7a s8 func /\
   fn_has_code s8 s9 func /\ fn_has_code s9 s10 func /\
   fn_has_code s11 s11a func /\ fn_has_code s11a s12 func /\
   fn_has_code s12 s13 func /\ fn_has_code s13 s14 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `local_ptrs_reserved ce s7 /\ local_ptrs_reserved ce s11` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx))
     expr_res_ok es` by
    (drule ifexp_forced_condition_admissible >>
     simp[gas_admissible_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_def] >> disch_then drule_all >> strip_tac >>
  rewrite_tac[ifexp_forced_source] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  suspend "condition_outcome"
QED

Resume widened_ifexp_vv_sim[condition_outcome]:
  reverse conj_tac >-
    (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
     metis_tac[expr_exit_INR_type]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  `vyperState$bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (fs[gas_marked_exec_def] >> metis_tac[listTheory.APPEND_NIL]) >>
  `?sel. v = BoolV sel` by
    (drule ifexp_forced_condition_admissible >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `v` >> simp[] >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[cj 1 gas_path_normal]) >>
  `eval_operand cond_op t = SOME (if sel then 1w else 0w)` by
    (qpat_x_assum `expr_post _ _ _ _ c _ _ _ _ _ _ _ _` mp_tac >>
     `post_value_type ce c = BaseT BoolT` by
       metis_tac[post_value_type_word, is_word_type_def] >>
     simp[expr_post_def, expr_val_rel_def, is_word_type_def,
       evaluate_type_def, typed_val_to_w256_def, val_to_w256_def]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to (if sel then tl else el) t))` by
    (simp[gas_marked_path_def] >> irule assert_jnz_zero_path >>
     simp[] >> qexistsl_tac [`cond_op`, `s5`, `s6`] >>
     qpat_assum `emit_inst JNZ _ _ _ = _` (mp_tac o MATCH_MP emit_inst_extends) >>
     strip_tac >> simp[]) >>
  `gas_admissible
     (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
     expr_vv_res_ok (mid with gas_obs := [])` by
    (irule ifexp_marked_branch_admissible >> metis_tac[]) >>
  `expr_body_pre ce cx env (if sel then a else b) (mid with gas_obs := []) /\
   expr_vv_sim ctx func ce cx ty (if sel then a else b) (mid with gas_obs := [])` by
    metis_tac[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) t` by
    metis_tac[expr_post_state] >>
  suspend "selected_branch"
QED

Resume widened_ifexp_vv_sim[selected_branch]:
  Cases_on `sel` >> gvs[] >>
  drule_at (Pat `expr_vv_sim _ _ _ _ _ _ _`) selected_ifexp_arm_outcome >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >>
  disch_then assume_tac >>
  `!lbl. local_ptrs_rel func ce mid.scopes (jump_to lbl t)` by
    (gen_tac >> `stmt_state_rel ctx func ce cx mid (jump_to lbl t)` by
      simp[stmt_state_rel_jump_to] >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  qmatch_asmsub_rename_tac `gas_marked_path F ctx func t 0 (OK (jump_to lbl t))` >>
  qpat_x_assum `!s0' env' c' b' a'. _`
    (qspec_then `jump_to lbl t` mp_tac) >>
  disch_then (qspec_then `env` mp_tac) >>
  disch_then (qspecl_then [`c`, `b`, `a`] mp_tac) >>
  (impl_tac >- (simp[stmt_state_rel_jump_to, jump_to_def] >>
    metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans])) >>
  disch_then assume_tac >>
  irule gas_outcome_zero_prefix_any >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  irule normalized_arm_join_outcome >>
  simp[] >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Finalise widened_ifexp_vv_sim
