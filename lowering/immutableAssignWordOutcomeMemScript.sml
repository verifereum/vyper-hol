(* Memory-checked statement outcome for a word-valued immutable store. *)
Theory immutableAssignWordOutcomeMem
Ancestors
  immutableAssignCompose immutableStoreOptionPathMem immutableAssignStore
  immutableDeployAssignFacts immutableDeployAssignAdmissible
  immutableStoreOptionMem exprSimProps venomMemProps
  exprLoweringProps loweringStateRelDefs compileEnv stmtLowering context
  venomState venomExecSemantics valueEncodingProps immutableEncoding
  finite_map words list

Theorem immutable_assign_word_stmt_post_mem:
  compile_assign_value ce (Lit (n2w off)) LocCode op T loc ity sty bytes su = ((),sb) /\
  fn_has_code su sb func /\ ~block_is_terminated sb /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  stmt_state_rel ctx func ce cx ee s /\ expr_sim_inv ce cx env ee /\
  local_ptrs_reserved ce su /\ ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ is_word_type ity /\
  value_has_type itv v /\ off < dimword (:256) /\
  write_place cx (ImmutablePlace ce.ce_module id []) v ee = (INL (),fin) /\
  (!x. op = Var x ==> not_fresh_at su x) /\
  eval_operand op s = SOME (typed_val_to_w256 itv v) ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    stmt_post ctx func cx lctx ce ce su sb ee s (INL ()) fin q
Proof
  strip_tac >>
  `!region. ce.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w` by
    fs[stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  `compile_imm_store_word ce.ce_imm_alloca (Lit (n2w off)) op su = ((),sb)` by
    fs[compile_assign_value_def, comp_bind_def, comp_return_def] >>
  `type_memory_size itv = 32` by metis_tac[word_tv_memory_size] >>
  `w2n (n2w off:bytes32) + 32 <= s.vs_alloca_next` by
    (drule_all immutable_assign_declared_region >> simp[]) >>
  drule_all immutable_assign_word_store >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all immutable_store_option_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `t = u` by fs[] >> qpat_x_assum `t = u` SUBST_ALL_TAC >>
  qexists_tac `u with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  `same_blocks su sb` by
    (drule immutable_store_option_code >> simp[]) >>
  `u.vs_halted = s.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
   (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
     vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
     vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_memory := _; vs_immutables := _|> = s`
       mp_tac >> simp[venom_state_component_equality]) >>
  irule immutable_assign_suffix_stmt_post >>
  simp[LENGTH_mstore_eq, lookup_var_def] >>
  conj_tac >- fs[same_blocks_def] >>
  qexistsl_tac [`env`,`id`,`itv`,`ity`,`off`,`v`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> simp[] >> irule mstore_mem_bytes_at_disjoint >>
      fs[regions_disjoint_def] >> decide_tac) >>
  metis_tac[evaluated_immutable_admissible]
QED
