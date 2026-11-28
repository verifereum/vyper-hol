(* Package the recorded MakeArray endpoint, including its own buffer. *)
Theory bodyFullMakeArrayResult
Ancestors
  bodyFullMakeArrayResultDefs exprSimAggregateChildren exprSimAggregateSource
  exprSimBuffer exprSimProps exprLoweringProps exprSimMemDefs
  exprSimHyps loweringPosts bodyPtrDefs compileEnv context valueEncoding
  vyperInterpreter vyperState venomState venomInst fragExec words
  bodyFullHashKeccakFixed bodySimStmtFacts[qualified] exprSimHypsDefs vyperTypeInvariants

val _ = Parse.hide "base";

Theorem make_array_packaging_internal[local]:
  make_array_packaging_ok
Proof
  rewrite_tac[make_array_packaging_ok_def] >> rpt gen_tac >> strip_tac >>
  fs[make_array_completed_def] >>
  qpat_x_assum `e = Builtin _ _ _` (fn th => rewrite_tac[GSYM th]) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `base < dimword (:256)` by decide_tac >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def, read_result_def, return_def] >>
  `expr_body_pre_mods ce.ce_modules ce cx env e (es with gas_obs := gs)` by
    fs[expr_body_pre_mods_def] >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_all_then strip_assume_tac
       (REWRITE_RULE [ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval_mods) >> simp[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_mods_def, expr_sim_inv_mods_def, env_consistent_def,
       env_context_consistent_def] >>
  `val_wf tv v` by
    (gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_then ACCEPT_TAC (cj 1 typed_value_wf)) >>
  `val_footprint tv v <= cap /\ val_store_size tv v <= cap` by
    metis_tac[val_footprint_le,val_store_size_le] >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 t` by
    (strip_tac >> irule aggregate_pure_frame_buffer >> conj_tac
     >- (qexistsl [`cap`,`base`,`sm`,`si`] >> simp[] >> metis_tac[]) >>
     metis_tac[]) >>
  `val_in_memory tv v base t.vs_memory` by
    (qpat_x_assum `!m. mem_agree_outside _ _ _ ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `vv_post H ctx func ce cx e es sa sb s0 ee (Value v)
     (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t` by
    (irule buffer_memory_vv_post_general >>
     simp[mk_ptr_def,eval_operand_def,wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD] >>
     fs[wb_frame_def,ci_mono_def,loweringStateRelDefsTheory.regions_disjoint_def] >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v)
     (LocatedValue (expr_type e) (mk_ptr (Var q) LocMemory)) t` by
    (asm_rewrite_tac[] >>
     drule exprSimMemDefsTheory.vv_store_bound_capacity >>
     disch_then irule >>
     simp[mk_ptr_def,eval_operand_def,arithmeticTheory.LESS_MOD]) >>
  drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
  gs[mk_ptr_def,vv_location_def] >>
  conj_tac
  >- (simp[ptr_vv_ok_def,read_result_def,return_def,
           ptr_mem_ok_def,eval_operand_def,arithmeticTheory.LESS_MOD] >>
      gvs[ptr_covers_def,arithmeticTheory.LESS_MOD] >> decide_tac) >>
  conj_tac
  >- (simp[vv_own_def,read_result_def,return_def,eval_operand_def] >>
      strip_tac >> disj1_tac >> qexistsl [`sa.cs_next_id`,`base`,`cap`] >>
      simp[wordsTheory.w2n_n2w,arithmeticTheory.LESS_MOD] >>
      fs[ci_mono_def,loweringStateRelDefsTheory.regions_disjoint_def] >>
      first_assum ACCEPT_TAC) >>
  gvs[ptr_buf_ok_def,ptr_covers_def,eval_operand_def]
QED

Theorem make_array_completed_full:
  ^(rhs (concl (PURE_REWRITE_RULE [make_array_completed_def]
    make_array_packaging_ok_def)))
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [make_array_packaging_ok_def, make_array_completed_def]
    make_array_packaging_internal)
QED
