(* Physical resources for the ABI row driver at the linked buffer's live cut. *)
Theory bodyAbiTupleBufferResourcesMods
Ancestors
  bodyAbiTupleBufferStateMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  stateRelProj exprLoweringProps venomMemDefs ptrDiscipline context words
Libs horizonTypeLib

Theorem abi_tuple_buffer_resources_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (?H. valid_horizon cx st0 H ee.storage_trace) ==>
  alloca_inv u /\ alloca_room ctx func u /\ allocas_from lo u /\
  lo <= u.vs_alloca_next /\ ~u.vs_halted /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp)
Proof
  rewrite_tac[abi_tuple_buffer_state_mods_def] >>
  disch_then strip_assume_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stmt_state_rel_alloca_room >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_then assume_tac stmt_state_rel_fmp_room >>
  qpat_x_assum `ghost_inv_at_mods _ lo _ _ _ _ _ _ u`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  simp[] >> strip_tac >>
  qpat_x_assum `fmp_room ctx func u` (mp_tac o REWRITE_RULE[fmp_room_def]) >>
  simp[] >> decide_tac
QED
