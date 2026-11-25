(* Restore the linked state relations at the ECAdd input packet cursor. *)
Theory bodyECAddPayloadFrameMods
Ancestors
  exprSimPtrLiteralBuffer bodyIfExpTypedImmFrameMods bodyIfExpTypedGhostMods
  stateRelProj exprLoweringProps typedMemoryCopy loweringStateRelDefs
  compileEnv venomState venomInst ptrDiscipline pred_set words

Theorem ecadd_payload_frame_mods:
  stmt_state_rel H ctx func ce cx ee s /\
  immutable_frame_mods func ce cx ee s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  MEM (mk_inst aid ALLOCA [Lit 128w] [dst]) (fn_insts func) /\
  FLOOKUP s.vs_allocas aid = SOME (b,128) /\ lo <= b /\
  (!name p n. local_region ce ee.scopes s name p n ==> regions_disjoint b 128 p n) /\
  t = r with vs_inst_idx := LENGTH cpayload.cs_current_insts /\
  (r with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!p n. regions_disjoint b 128 p n ==>
         mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
  (!z. not_fresh_at ca z ==> lookup_var z t = lookup_var z s /\
         FLOOKUP G' z = FLOOKUP G z /\ op_taint tn' (Var z) = op_taint tn (Var z)) /\
  tn'.t_mem = tn.t_mem DIFF {i | b <= i /\ i < b+128} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
  ghost_inv_at_mods D lo d ce cx ee G' tn' t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!p n. regions_disjoint b 128 p n ==>
         mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >>
  `typed_copy_state_frame ca b 128 s t` by
    (pure_rewrite_tac[typed_copy_state_frame_def, typed_copy_frame_def] >>
     conj_tac
     >- (qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = s` mp_tac >>
         simp[venom_state_component_equality]) >>
     conj_tac
     >- (rpt strip_tac >> qpat_assum `!z. not_fresh_at ca z ==> _` drule >> simp[]) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!p n. regions_disjoint b 128 p n ==> _` irule >>
     fs[regions_disjoint_def]) >>
  conj_tac
  >- (`stmt_state_rel H ctx func ce cx ee r` by
        (irule literal_ptr_state_memory_frame >>
         qexistsl_tac [`aid`,`b`,`128`,`dst`,`ca`,`ca`,`s`] >> simp[] >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qpat_x_assum `t = r with vs_inst_idx := _` SUBST_ALL_TAC >>
         qpat_assum `typed_copy_state_frame _ _ _ _ _`
           (strip_assume_tac o SRULE [typed_copy_state_frame_def,typed_copy_frame_def,lookup_var_def]) >>
         simp[lookup_var_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[stmt_state_rel_inst_idx]) >>
  conj_tac
  >- (irule ifexp_typed_immutable_frame_mods >>
      qexistsl_tac [`b`,`mk_inst aid ALLOCA [Lit 128w] [dst]`,`ca`,`128`,`s`] >>
      simp[mk_inst_def]) >>
  conj_tac
  >- (irule ifexp_typed_copy_ghost_mods >>
      qexistsl_tac [`G`,`b`,`func`,`ca`,`128`,`s`,`tn`] >> simp[IN_DIFF] >>
      metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  qpat_assum `(r with <|vs_vars := _; vs_memory := _|>) = s`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  first_assum ACCEPT_TAC
QED
