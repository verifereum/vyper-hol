(* Body-state preservation across typed copying and its control flow. *)
Theory typedCopyBodyFrame
Ancestors
  typedMemoryCopy exprSimBufferStore exprLoweringProps
  loweringPosts compileEnv venomState venomMemDefs

Theorem body_state_control_frame[local]:
  stmt_state_rel ctx func ce cx es
    (s with <|vs_prev_bb := pb; vs_current_bb := bb; vs_inst_idx := ix|>) <=>
  stmt_state_rel ctx func ce cx es s
Proof
  `fmp_room ctx func
      (s with <|vs_prev_bb := pb; vs_current_bb := bb; vs_inst_idx := ix|>) <=>
    fmp_room ctx func s` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, lookup_var_def, storage_rel_def,
       transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, alloca_inv_def,
       allocas_non_overlapping_def, alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def,
       immutable_base_zero_alt]
QED

Theorem typed_copy_body_state_frame:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  typed_copy_state_frame sa dst n s q /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b + sz <= dst \/ dst + n <= b) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) dst n) ==>
  stmt_state_rel ctx func ce cx es q
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `typed_copy_state_frame sa dst n s q` >>
  qpat_x_assum `typed_copy_state_frame _ _ _ _ _` mp_tac >>
  simp[typed_copy_state_frame_def, typed_copy_frame_def] >> strip_tac >>
  `stmt_state_rel ctx func ce cx es
     (q with <|vs_prev_bb := s.vs_prev_bb;
               vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>)` suffices_by
    simp[body_state_control_frame] >>
  irule buffer_store_state_frame >>
  qexistsl_tac [`dst`, `n`, `s`, `sa`] >>
  gvs[lookup_var_def] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
