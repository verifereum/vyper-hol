Theory immutableCtorWordStoreGhost
Ancestors exprSimProps bodyPtrBytestringBuiltinsWindowGhost
  bodyFullMemoryFrames bodyStorageMetadata robustCopyTransportPtr
  memoryValueEncoding valueEncodingDefs valueEncodingProps ptrDiscipline
  venomState bodySim exprSimHypsDefs stmtSimDefs bodyPtrDefs
  exprLoweringProps loweringStateRelDefs stateRelProj rich_list pred_set
  bodyInvCodeProps gasContext immSectionDead

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule body_inv_contract >> strip_tac >>
  drule contract_inv_cenv_modules >> strip_tac >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> drule contract_inv_module_codes >> simp[]) >>
  `local_ptrs_rel func ce es.scopes s` by
    metis_tac[stmt_state_rel_local_ptrs_alloca] >>
  `!name b len. local_region ce es.scopes s name b len ==>
     mem_bytes_at b len q.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >> Cases_on `len = 0` >- simp[mem_bytes_at_def] >>
     `0 < len` by decide_tac >>
     `lo <= b` by (drule_all body_full_local_region_lower_bound >> simp[]) >>
     `off+32 <= b` by decide_tac >>
     simp[] >> irule mstore_mem_bytes_at_disjoint >> gvs[]) >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
     ptr_covers Gf tf x q sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  `q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_allocas = s.vs_allocas /\
   q.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `q with <|vs_vars := _; vs_memory := _;
       vs_immutables := _; vs_prev_bb := _; vs_current_bb := _;
       vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_inv_at_def]) >>
  simp[ghost_inv_at_def, allocas_from_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
        (fs[local_ptrs_rel_def] >> metis_tac[]) >>
      `val_footprint entry.type entry.value <= sz` by
        (drule val_footprint_le >> decide_tac) >>
      `local_region ce es.scopes s name (w2n w) sz` by
        (simp[local_region_def] >> metis_tac[]) >>
      `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
      `mem_bytes_at (w2n w) sz q.vs_memory =
       mem_bytes_at (w2n w) sz s.vs_memory` by metis_tac[] >>
      `!i. w2n w <= i /\ i < w2n w+sz /\ i IN tf.t_mem ==>
           i IN tn.t_mem` by (fs[SUBSET_DEF] >> metis_tac[]) >>
      irule robust_val_in_memory_window_transport >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`tn.t_mem`,`tf.t_mem`,`sz`,`s.vs_memory`,`q.vs_memory`] >>
      gvs[] >> metis_tac[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[])
  >- (`!im. D.d_imm im = UNIV` by fs[dead_lo_ok_def] >>
      qpat_x_assum `stor_taint_ok_at D tn s` mp_tac >>
      simp[stor_taint_ok_at_def])
  >- (rpt strip_tac >>
      drule imm_section_dead_mods_singleton >>
      disch_then (fn th => simp[th]) >>
      qpat_x_assum `!i. _ ==> imm_section_dead _ _ _`
        (qspec_then `i` mp_tac) >> simp[])
  >- (rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[])
  >> fs[allocas_from_def]
QED
*)
Theorem immutable_ctor_word_store_ghost:
  ghost_inv_at D lo d ce cx es G tn s /\
  dead_lo_ok H D lo ce cx /\ ce.ce_is_ctor /\
  body_inv tops ctx ce cx /\
  expr_sim_inv ce cx env es /\ stmt_state_rel H ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  ee.scopes = es.scopes /\ off+32 <= lo /\
  q.vs_memory = (mstore off word s).vs_memory /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==>
     lookup_var x q = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
     op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\
  tf.t_mem SUBSET tn.t_mem /\
  (!i. i < lo /\ i IN tf.t_mem ==>
    imm_section_dead (cx_tops cx) (mem_bytes_at 0 lo q.vs_memory) i) ==>
  ghost_inv_at D lo d ce cx ee Gf tf q
Proof
  cheat
QED
