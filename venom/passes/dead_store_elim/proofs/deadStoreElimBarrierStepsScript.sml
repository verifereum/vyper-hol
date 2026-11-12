Theory deadStoreElimBarrierSteps
Ancestors
  deadStoreElimOpcodeCoverage deadStoreElimLocal deadStoreElimStructure
  deadStoreElimPending deadStoreElimLiveness deadStoreElimDefs deadStoreElimEquiv
  venomExecSemantics venomWf venomInst venomEffects stateEquiv basePtrDefs memLocDefs

Definition dse_barrier_case_def:
  dse_barrier_case sp opc <=>
    (sp = AddrSp_Memory /\ opc IN {ILOAD; INVOKE; RET; DRET; RETFMP; MEMTOP}) \/
    (sp IN {AddrSp_Storage; AddrSp_Transient} /\
     opc IN {CALL; STATICCALL; DELEGATECALL; INVOKE; CREATE; CREATE2;
             RETURN; STOP; SINK; SELFDESTRUCT; RET; DRET; RETFMP})
End

Theorem dse_barrier_read_location:
  dse_barrier_case sp inst.inst_opcode ==>
  bp_get_read_location bp inst sp = ml_undefined
Proof
  pure_rewrite_tac[dse_barrier_case_def] >> strip_tac
  >- (gvs[] >> irule dse_memory_barrier_read_location >> simp[]) >>
  irule dse_key_barrier_read_location >> simp[]
QED

Theorem dse_local_agrees_undefined_read_instruction:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  bp_get_read_location bp inst sp = ml_undefined ==> s = t
Proof
  strip_tac >> irule dse_local_agrees_undefined_read >>
  fs[get_instruction_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem dse_barrier_inputs:
  dse_barrier_case sp inst.inst_opcode /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst ==> s = t
Proof
  strip_tac >> irule dse_local_agrees_undefined_read_instruction >>
  drule dse_barrier_read_location >> metis_tac[]
QED

Theorem dse_barrier_ok:
  dse_barrier_case sp inst.inst_opcode /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK s1 ==>
  step_inst fuel ctx inst t = OK s1 /\
  dse_local_agrees sp [] (s1 with vs_inst_idx := idx)
    (s1 with vs_inst_idx := idx) /\
  dse_pending_at cfg' bp' sp fn' bb' idx' [] s1
Proof
  strip_tac >> drule_all dse_barrier_inputs >> strip_tac >>
  gvs[dse_local_agrees_refl, dse_pending_at_empty]
QED

Theorem dse_barrier_result:
  dse_barrier_case sp inst.inst_opcode /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  (?e. step_inst fuel ctx inst s = Error e) \/
  lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp)
    (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  strip_tac >> drule_all dse_barrier_inputs >> strip_tac >> gvs[] >>
  Cases_on `step_inst fuel ctx inst s` >>
  simp[lift_result_def, dse_equiv_refl]
QED

Theorem dse_barrier_effects_exclusion:
  dse_barrier_case sp inst.inst_opcode ==>
  ~(is_memory_def_opcode sp inst.inst_opcode /\ effects_in_space sp inst)
Proof
  simp[dse_barrier_case_def] >> strip_tac >>
  gvs[is_memory_def_opcode_def, is_terminator_def, write_effects_def,
      empty_effects_def, all_effects_def, effects_in_space_def]
QED

Theorem dse_barrier_retained:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  MEM inst (fn_insts fn) /\ dse_barrier_case sp inst.inst_opcode ==>
  dse_inst ids sp inst = inst
Proof
  strip_tac >> Cases_on `inst.inst_id IN ids`
  >- (drule_all all_dead_stores_occurrence >> strip_tac >>
      drule dse_barrier_effects_exclusion >> simp[]) >>
  simp[dse_inst_def]
QED
