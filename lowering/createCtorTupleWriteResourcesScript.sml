Theory createCtorTupleWriteResources
Ancestors
  createCtorTupleWrite exprSimLiteralBuffer exprSimProps freshWrites
  abiBytestringAllocation
  loweringPosts exprLoweringProps loweringStateRelDefs venomMemDefs venomState arithmetic

Theorem ctor_physical_write_resources:
  (if is_word_type ty then emit_void MSTORE [dst; op]
   else if is_bytestring_type ty then compile_store_bytestring op dst
   else emit_void MCOPY [dst; op; Lit (n2w (type_memory_bytes ce ty))]) ca = ((),cb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  eval_operand op s = SOME sw /\ eval_operand dst s = SOME dw /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) /\
  (!x. op = Var x \/ dst = Var x ==> not_fresh_at ca x) /\
  fn_has_code ca cb func /\ ~s.vs_halted /\
  s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts /\
  stmt_state_rel H ctx func ce cx es s /\ local_ptrs_reserved ce cut /\
  cut.cs_next_var <= ca.cs_next_var /\
  FLOOKUP s.vs_allocas site = SOME (b0,n0) /\ cut.cs_next_id <= site /\
  b0 <= w2n dw /\ w2n dw + type_memory_size tv <= b0+n0 /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
     b+sz <= b0 \/ b0+n0 <= b) /\
  (ce.ce_is_ctor ==> !name tv' v' off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv',v') ==>
    loweringStateRelDefs$regions_disjoint off (type_memory_size tv') b0 n0) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory tv v (w2n dw) q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = cb.cs_current_bb /\
    q.vs_inst_idx = LENGTH cb.cs_current_insts /\
    stmt_state_rel H ctx func ce cx es q /\
    alloca_inv q /\ alloca_room ctx func q /\ fmp_room ctx func q /\
    wb_frame ce es es cut s q /\
    q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
    (!x. not_fresh_at ca x ==> lookup_var x q = lookup_var x s) /\
    (!a n. a+n <= w2n dw \/ w2n dw + type_memory_size tv <= a ==>
      mem_bytes_at a n q.vs_memory = mem_bytes_at a n s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_prev_bb := s.vs_prev_bb;
      vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >> drule_all ctor_physical_write_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `!x. not_fresh_at cut x ==> lookup_var x q = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  `!name b sz. local_region ce es.scopes s name b sz ==>
    b+sz <= w2n dw \/ w2n dw + type_memory_size tv <= b` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz s.vs_memory` by
    metis_tac[] >>
  `wb_frame ce es es cut s q` by
    (rw[wb_frame_def]
     >- gvs[venom_state_component_equality]
     >- (qpat_assum `!a n. _ ==> mem_bytes_at a n q.vs_memory = _` irule >>
         irule abiBytestringAllocationTheory.allocated_windows_disjoint >>
         qexistsl_tac [`off`, `aid`, `sz`, `s`, `b0`, `site`, `n0`] >>
         fs[alloca_inv_def] >> decide_tac) >>
     irule locals_kept_regions >> gvs[]) >>
  `stmt_state_rel H ctx func ce cx es
    (q with <|vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
      vs_inst_idx := s.vs_inst_idx|>)` by
    (irule literal_state_memory_frame >> qexists_tac `s` >> simp[] >>
     conj_tac >- gvs[] >>
     conj_tac
     >- (rpt strip_tac >> simp[lookup_var_def] >>
         fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
     conj_tac
     >- (rpt strip_tac >> simp[lookup_var_def] >>
         fs[local_ptrs_reserved_def, lookup_var_def] >> metis_tac[]) >>
     conj_tac >- gvs[] >>
     rpt strip_tac >>
     qpat_assum `!a n. _ ==> mem_bytes_at a n q.vs_memory = _` irule >>
     first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `stmt_state_rel H ctx func ce cx es q` by
    (pop_assum mp_tac >>
     simp_tac (srw_ss()) [stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def,
       loweringStateRelDefsTheory.storage_rel_def,
       loweringStateRelDefsTheory.transient_rel_def,
       loweringStateRelDefsTheory.immutables_rel_def,
       loweringStateRelDefsTheory.logs_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt, fmp_room_def,
       loweringStateRelDefsTheory.accounts_rel_def] >> strip_tac >> fs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists_tac `q` >>
  gvs[venom_state_component_equality, stmt_state_rel_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
