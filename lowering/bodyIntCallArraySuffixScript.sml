(* Fixed-array indexing constructs a single counted suffix endpoint. *)
Theory bodyIntCallArraySuffix
Ancestors
  exprSimArrayIndex fragGasFresh freshWrites varsExt exprLowering
  exprLoweringProps compileEnv venomState venomExecSemantics

Theorem straight_fresh_fixed_array_subscript:
  straight_fresh (compile_array_subscript base_op idx F cnt ws esz sgn loader)
Proof
  `compile_array_subscript base_op idx F cnt ws esz sgn loader =
   comp_ignore_bind (array_bounds_check idx (Lit (n2w cnt)) sgn)
     (array_elem_ptr base_op idx F ws esz)` by
    simp[FUN_EQ_THM, compile_array_subscript_split, comp_bind_def,
         comp_return_def] >>
  asm_rewrite_tac[] >> MATCH_ACCEPT_TAC straight_fresh_array_check_ptr
QED

Theorem fixed_array_subscript_success_path:
  compile_array_subscript base_op idx F cnt ws esz sgn loader sa = (p,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op (drop_fresh sa s) = SOME b /\
  eval_operand idx (drop_fresh sa s) = SOME i /\
  idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand p t = SOME (b + i * n2w esz) /\
      (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
             lookup_var z t = SOME v) /\
      (!aid buf. FLOOKUP s.vs_allocas aid = SOME buf ==>
                 FLOOKUP t.vs_allocas aid = SOME buf) /\
      t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx F cnt ws esz sgn loader)` by
    simp[straight_fresh_fixed_array_subscript] >>
  drule compile_array_subscript_ok >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh, array_len_ok_static] >>
  disch_then (qspec_then `n2w cnt` mp_tac) >>
  simp[array_len_ok_static] >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[]
QED

Theorem fixed_array_subscript_abort_path:
  compile_array_subscript base_op idx F cnt ws esz sgn loader sa = (p,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand base_op (drop_fresh sa s) = SOME b /\
  eval_operand idx (drop_fresh sa s) = SOME i /\
  ~idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx F cnt ws esz sgn loader)` by
    simp[straight_fresh_fixed_array_subscript] >>
  drule compile_array_subscript_oob >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >>
  disch_then (qspec_then `n2w cnt` mp_tac) >>
  simp[array_len_ok_static] >> strip_tac >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any)
QED
