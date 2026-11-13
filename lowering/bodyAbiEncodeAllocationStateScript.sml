(* Body-state framing for a singleton allocation window, fresh or reused. *)
Theory bodyAbiEncodeAllocationState
Ancestors
  bodyAbiEncodeResultMemory abiEncoderWindowContract abiEncoderWindowPhase
  abiEncoderWindowMemFrame abiEncoderRegisteredEffect abiCallerLocalScratch
  localPtrsProps exprSimProps exprSimAlloc compileEnv loweringPosts exprLoweringProps loweringStateRelDefs
  venomState venomInst venomMemDefs valueEncoding finite_map pred_set words list arithmetic

Theorem abi_encode_word_stage_local_bytes:
  stmt_state_rel ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce ee.scopes q /\
  window_phase ctx func st en {inst.inst_id} [] s t /\
  local_region ce ee.scopes s name b sz ==>
  mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func ce ee.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `b+sz <= s.vs_alloca_next` by
    (drule_all abi_caller_local_end >> simp[]) >>
  drule window_phase_resources >> strip_tac >>
  irule window_alloca_growth_frame >> simp[] >>
  qexistsl [`{inst.inst_id}`, `[]`] >>
  simp[] >> reverse conj_tac >- metis_tac[window_phase_effect] >>
  rpt strip_tac >> gvs[] >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encode_word_stage_immutable_bytes[local]:
  stmt_state_rel ctx func ce cx ee s /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  window_phase ctx func st en {inst.inst_id} [] s t /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory
Proof
  strip_tac >>
  `immutable_alloca_sep func ce cx ee s` by fs[stmt_state_rel_def] >>
  qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
  simp[immutable_alloca_sep_def] >> strip_tac >>
  qpat_x_assum `!name tv v off. _ ==> _` drule_all >> strip_tac >>
  drule window_phase_resources >> strip_tac >>
  irule window_alloca_growth_frame >> simp[] >>
  qexistsl [`{inst.inst_id}`, `[]`] >> simp[] >>
  reverse conj_tac >- metis_tac[window_phase_effect] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def, venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encode_word_stage_state:
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce st /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
  inst.inst_outputs = [q] /\ not_local_ptr ce ee.scopes q /\
  window_phase ctx func st en {inst.inst_id} [] s t /\
  window_mem_frame ctx func s t /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (b,n) /\ n < dimword (:256) /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory ==>
  stmt_state_rel ctx func ce cx ee t
Proof
  strip_tac >>
  `!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s` by
    (rpt strip_tac >>
     `?w. lookup_var p s = SOME w` by
       (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
     `not_fresh_at st p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[window_phase_vars]) >>
  `!p. ce.ce_imm_alloca = SOME (Var p) ==> lookup_var p t = lookup_var p s` by
    (rpt strip_tac >>
     `lookup_var p s = SOME 0w` by
       fs[stmt_state_rel_def, immutable_base_zero_def, eval_operand_def] >>
     metis_tac[local_ptrs_reserved_imm_base, window_phase_vars]) >>
  irule abi_encode_result_state >>
  qpat_assum `window_phase _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `inst' = inst` by metis_tac[localPtrsPropsTheory.fn_inst_ids_distinct_inj] >>
      gvs[]) >>
  conj_tac >- metis_tac[abi_encode_word_stage_local_bytes] >>
  conj_tac
  >- (rpt strip_tac >> fs[local_region_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[abi_encode_word_stage_immutable_bytes] >>
  metis_tac[abi_encode_word_stage_immutable_bytes]
QED

Theorem abi_encode_singleton_wb_frame:
  stmt_state_rel ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce ee.scopes q /\ inst.inst_id = st.cs_next_id /\
  window_phase ctx func st en {inst.inst_id} [] s t ==>
  wb_frame ce ee ee st s t
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `!name b sz. local_region ce ee.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    metis_tac[abi_encode_word_stage_local_bytes] >>
  simp[wb_frame_def] >> conj_tac >- metis_tac[window_phase_vars] >>
  conj_tac >- metis_tac[window_phase_effect, abi_encoder_registered_effect_allocated] >>
  reverse conj_tac >- metis_tac[locals_kept_regions] >>
  rpt strip_tac >> irule window_alloca_growth_frame >>
  drule window_phase_resources >> strip_tac >>
  conj_tac >- metis_tac[allocaSiteResourceTheory.alloca_site_registered_below] >>
  simp[] >> qexistsl [`{inst.inst_id}`, `[]`] >> simp[] >>
  reverse conj_tac >- metis_tac[window_phase_effect] >>
  rpt strip_tac >> gvs[] >>
  `aid <> inst.inst_id` by decide_tac >>
  metis_tac[allocaSiteResourceTheory.alloca_site_registered_disjoint]
QED
