(* Memory-checked statement outcome for a direct composite immutable copy. *)
Theory immutableAssignDirectOutcomeMem
Ancestors
  immutableAssignCompose immutableAssignStore immutableFixedOptionPathMem
  immutableDeployAssignFacts immutableDeployAssignAdmissible
  immutableAssignStoreLength immutableDeployOperandTransfer exprLoweringProps
  loweringStateRelDefs stmtSimDefs compileEnv stmtLowering context
  venomState venomMemProps exprSimProps valueEncodingProps immutableEncoding
  finite_map words list divides

Theorem immutable_assign_direct_stmt_post_mem:
  compile_assign_value ce (Lit (n2w off)) LocCode op F loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  ity = sty /\ ~is_bytestring_type ity /\
  copy_size = (if is_bytestring_type ity then type_memory_bytes ce sty else bytes) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) /\
  32*n <= type_memory_size itv /\
  value_has_type itv v /\ value_has_type stv v /\
  val_in_memory stv v a s.vs_memory /\ val_footprint stv v <= k /\
  k <= 32*n /\ a+k < dimword (:256) /\ off+32*n < dimword (:256) /\
  a+32*n <= s.vs_alloca_next /\
  (a+32*n <= off \/ off+32*n <= a) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  (!region x. ce.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (n2w a) ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  `a+k <= off \/ off+32*n <= a` by decide_tac >>
  drule immutable_assign_direct_store >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ity = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ ity = _`)) >>
  disch_then (qspecl_then [`n`,`k`,`ce.ce_imm_alloca`,`ctx`,`copy_size`,`off`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `compile_imm_store_words ce.ce_imm_alloca op (Lit (n2w off)) n 0 su = ((),sb)` by
    (qpat_x_assum `n = _` (fn th => rewrite_tac[th]) >>
     irule immutable_store_suffix_words >>
     fs[compile_assign_value_def, comp_bind_def, comp_return_def] >>
     gvs[comp_return_def]) >>
  `0 < n` by
    (qpat_x_assum `n = _` (fn th => rewrite_tac[th]) >>
     rw[] >> irule DIV_POS >> decide_tac) >>
  `off+32*n <= s.vs_alloca_next` by
    (drule_all immutable_assign_declared_region >> strip_tac >> decide_tac) >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `a+32*n < dimword (:256)` by decide_tac >>
  qpat_x_assum `n = _` kall_tac >>
  mp_tac (Q.INST [`imm` |-> `ce.ce_imm_alloca`, `src` |-> `op`,
    `dst` |-> `Lit (n2w off)`, `b` |-> `off`, `off` |-> `0`, `sa` |-> `su`]
    (SPEC_ALL immutable_fixed_copy_operand_mem_path_option)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `t = u` by fs[] >> qpat_x_assum `t = u` SUBST_ALL_TAC >>
  suspend "outcome"
QED

Resume immutable_assign_direct_stmt_post_mem[outcome]:
  markerLib.RESUME_TAC >> (
  `LENGTH s.vs_memory <= LENGTH u.vs_memory` by
    metis_tac[immutable_assign_store_words_memory_length] >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality] >> strip_tac >> simp[]) >>
  mp_tac (Q.INST [`q` |-> `u`] (SPEC_ALL immutable_assign_suffix_stmt_post)) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- metis_tac[evaluated_immutable_admissible] >>
      conj_tac
      >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >>
          fs[regions_disjoint_def] >> decide_tac) >>
      fs[same_blocks_def]) >> simp[])
QED

Finalise immutable_assign_direct_stmt_post_mem
