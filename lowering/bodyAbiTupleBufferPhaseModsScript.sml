(* Fixed-endpoint phase and composition rules for the linked tuple buffer. *)
Theory bodyAbiTupleBufferPhaseMods
Ancestors
  bodyAbiTupleBufferStateMods bodyAbiTupleSavedIntervalsMods bodyAbiTuplePhaseStateMods
  bodyAbiTuplePhaseEffectMods bodyAbiTupleEffectsGrowthMods bodyAbiTupleEffectsOldVarsMods
  bodyAbiTupleEffectSitesMods bodyAbiTupleRegisteredWritesMods
  abiEncoderWindowPhase exprSimAbiEncodeExecFrame bodyFullPostsMods
  exprLoweringProps compileEnv loweringStateRelDefs
  venomState venomInst finite_map pred_set list pair

(* A pure phase can preserve the buffer before the cursor site is certified. *)
Theorem abi_tuple_buffer_phase_state_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c ids outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
  EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule abi_tuple_phase_state_mods >>
  qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qexistsl [`explicit`,`PG`,`hz`] >> asm_rewrite_tac[] >>
  match_mp_tac (GEN_ALL abi_tuple_saved_intervals_phase_mods) >>
  qhdtm_assum `abi_tuple_buffer_state_mods` (irule_at Any) >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  qexists `hz` >> asm_rewrite_tac[]
QED

Theorem abi_tuple_buffer_phase_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  ci_mono a c /\ window_phase ctx func a c ids outs u v /\
  abi_encode_exec_frame func u v /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK v,Gv,tv)) /\
  (!x. not_fresh_at a x ==>
    FLOOKUP Gv x = FLOOKUP Gu x /\ op_taint tv (Var x) = op_taint tu (Var x)) /\
  tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\ tv.t_imm = tu.t_imm /\
  shared NOTIN ids /\ (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
  EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (cursor_site IN ids ==>
    cursor_site < c.cs_next_id /\ ?slot. FLOOKUP v.vs_allocas cursor_site = SOME (slot,32)) /\
  (!aid. aid IN ids /\ aid <> cursor_site ==> a.cs_next_id <= aid /\ aid < c.cs_next_id) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) ==>
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix c v Gv tv /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c v Gv tv
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  conj_tac >- drule_all_then ACCEPT_TAC abi_tuple_buffer_phase_state_mods >>
  irule abi_tuple_phase_effect_mods >>
  qhdtm_assum `window_phase` (irule_at Any) >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> metis_tac[pred_setTheory.IN_INSERT]
QED

Theorem abi_tuple_row_effects_trans_mods:
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu c z Gz tz /\
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    c z Gz tz e q Ge tq ==>
  abi_tuple_row_effects_mods ce ee func shared pbase capacity dst_offset cursor_site
    a u Gu tu e q Ge tq
Proof
  strip_tac >>
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ a u _ _ c z _ _`
    (mp_then (Pos hd) (drule_then strip_assume_tac) abi_tuple_effects_growth_trans_mods) >>
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ a u _ _ c z _ _`
    (mp_then (Pos hd) (drule_then strip_assume_tac) abi_tuple_effects_old_vars_trans_mods) >>
  pure_rewrite_tac[abi_tuple_row_effects_mods_def] >> asm_rewrite_tac[] >>
  irule abi_tuple_effect_sites_trans_mods >>
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ a u _ _ c z _ _` (irule_at Any) >>
  qpat_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ c z _ _ e q _ _` (irule_at Any) >>
  rpt gen_tac >> MATCH_ACCEPT_TAC abi_tuple_registered_writes_sequence_mods
QED
