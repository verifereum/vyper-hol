(* Pure memory frames for singleton registered encoder allocations. *)
Theory bodyAbiEncodeSingletonFrame
Ancestors
  bodyAbiEncodeAllocationState abiEncoderWindowPhase abiEncoderWindowContract
  loweringPosts loweringStateRelDefs venomMemDefs finite_map pred_set list

Theorem abi_encode_singleton_pure_frame:
  stmt_state_rel ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr ce ee.scopes q /\
  inst.inst_id = st.cs_next_id /\
  window_phase ctx func st en {inst.inst_id} [] s t ==>
  pure_frame ce func ee st s t
Proof
  strip_tac >> simp[pure_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule abi_encode_word_stage_local_bytes >>
      qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >>
      metis_tac[]) >>
  rpt strip_tac >> irule abi_encoder_window_effect_bytes >>
  qexistsl [`{inst.inst_id}`, `[]`] >>
  simp[] >> reverse conj_tac >- metis_tac[window_phase_effect] >>
  rpt strip_tac >>
  simp[venomMemDefsTheory.regions_disjoint_def] >>
  qpat_x_assum `!inst b sz. _ ==> _` (qspec_then `inst` mp_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED
