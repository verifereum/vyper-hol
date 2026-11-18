(* Package the recorded MakeArray endpoint, including its own buffer. *)
Theory bodyFullMakeArrayResult
Ancestors
  bodyFullMakeArrayResultDefs exprSimAggregateChildren exprSimAggregateSource
  exprSimBuffer exprSimProps exprLoweringProps exprSimMemDefs
  exprSimHyps loweringPosts bodyPtrDefs compileEnv context valueEncoding
  vyperInterpreter vyperState venomState venomInst fragExec words
  bodyFullHashKeccakFixed

val _ = Parse.hide "base";

Theorem make_array_packaging_internal[local]:
  make_array_packaging_ok
Proof
  rewrite_tac[make_array_packaging_ok_def] >> rpt gen_tac >> strip_tac >>
  fs[make_array_completed_def] >>
  qpat_x_assum `e = Builtin _ _ _` (fn th => rewrite_tac[GSYM th]) >>
  `post_value_type ce e = expr_type e` by metis_tac[post_value_type_lowered] >>
  `base < dimword (:256)` by decide_tac >>
  `val_wf tv v` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[read_result_def, return_def] >> metis_tac[]) >>
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
