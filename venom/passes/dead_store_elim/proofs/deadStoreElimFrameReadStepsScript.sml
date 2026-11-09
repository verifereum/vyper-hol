Theory deadStoreElimFrameReadSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimMemory deadStoreElimLiveness
  deadStoreElimSafety deadStoreElimEquiv deadStoreElimDefs deadStoreElimDloadGuard
  finite_map deadStoreElimStructure venomWf
  basePtrDefs memLocDefs venomExecSemantics venomState venomEffects venomInst list
  deadStoreElimFrame
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem exec_read0_common_update:
  f s = f t /\ exec_read0 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_read0 f inst t = OK (update_var out w t)
Proof
  simp[exec_read0_def] >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_read1_common_update:
  (!op. eval_operand op s = eval_operand op t) /\
  (!v. f v s = f v t) /\ exec_read1 f inst s = OK s1 ==>
  ?out w. s1 = update_var out w s /\
    exec_read1 f inst t = OK (update_var out w t)
Proof
  simp[exec_read1_def] >> strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem exec_read0_result_cases:
  (?s1. exec_read0 f inst s = OK s1) \/
  (?e. exec_read0 f inst s = Error e)
Proof
  simp[exec_read0_def] >> rpt (CASE_TAC >> simp[])
QED

Theorem exec_read1_result_cases:
  (?s1. exec_read1 f inst s = OK s1) \/
  (?e. exec_read1 f inst s = Error e)
Proof
  simp[exec_read1_def] >> rpt (CASE_TAC >> simp[])
QED

Theorem exec_gas_result_cases:
  (?s1. exec_gas inst s = OK s1) \/
  (?e. exec_gas inst s = Error e)
Proof
  simp[exec_gas_def] >> rpt (CASE_TAC >> simp[])
QED

Theorem dse_local_agrees_gas_readings:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_gas_readings := gs) (t with vs_gas_readings := gs)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
      dse_safety_agrees_def, dse_operational_agrees_def,
      dse_equiv_def, dse_pending_memory_def, dse_memory_byte_def,
      lookup_var_def]
QED

Definition dse_frame_read_opcode_def:
  dse_frame_read_opcode opc <=>
    opc IN {CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE; CHAINID;
      COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; GASLIMIT; BASEFEE; BLOBBASEFEE;
      BLOCKHASH; BLOBHASH; CALLDATASIZE; CALLDATALOAD; RETURNDATASIZE; CODESIZE; DLOAD}
End

Theorem dse_local_agrees_frame:
  dse_local_agrees sp P s t ==>
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\ s.vs_returndata = t.vs_returndata /\
  s.vs_code = t.vs_code /\ s.vs_data_section = t.vs_data_section /\
  s.vs_gas_readings = t.vs_gas_readings
Proof
  simp[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]
QED

Theorem dse_frame_read_common_update:
  dse_frame_read_opcode inst.inst_opcode /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = OK s1 ==>
  (?out w. s1 = update_var out w s /\
     step_inst fuel ctx inst t = OK (update_var out w t)) \/
  (?out w gs. s1 = update_var out w (s with vs_gas_readings := gs) /\
     step_inst fuel ctx inst t = OK (update_var out w (t with vs_gas_readings := gs)))
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  drule dse_local_agrees_frame >> strip_tac >>
  Cases_on `inst.inst_opcode = GAS`
  >- (gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
          exec_gas_def, AllCaseEqs()] >> metis_tac[]) >>
  fs[dse_frame_read_opcode_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  disj1_tac >>
  FIRST [irule exec_read0_common_update, irule exec_read1_common_update] >>
  simp[] >> metis_tac[]
QED

Theorem dse_frame_read_result_cases:
  dse_frame_read_opcode inst.inst_opcode ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  simp[dse_frame_read_opcode_def] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_read0_result_cases, exec_read1_result_cases,
       exec_gas_result_cases]
QED

(* Failed interface attempt, E0038: DLOAD has a nonempty static Memory
   write footprint. Preserved for diagnosis; this is not an exported lemma.
Theorem dse_frame_read_write_location:
  dse_frame_read_opcode inst.inst_opcode ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[dse_frame_read_opcode_def] >> strip_tac >> Cases_on `sp` >>
  gvs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def,
      empty_effects_def]
QED
*)

Theorem dse_frame_read_no_clobber:
  dse_frame_read_opcode inst.inst_opcode /\ ml_is_fixed loc /\
  loc.ml_size <> SOME 0 /\ ~dse_inst_reads_alias FEMPTY bp sp loc inst ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DLOAD`
  >- (irule dse_dload_no_read_no_clobber >> simp[]) >>
  fs[dse_frame_read_opcode_def] >> Cases_on `sp` >>
  gvs[dse_inst_clobbers_def, bp_get_write_location_def,
      is_raw_fmp_opcode_def, write_effects_def, empty_effects_def,
      ml_empty_def, completely_contains_def, ml_is_fixed_def] >>
  Cases_on `loc.ml_size` >> gvs[]
QED

Theorem dse_frame_read_pending_step:
  dse_frame_read_opcode inst.inst_opcode /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  get_instruction bb idx = SOME inst /\
  s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s1
Proof
  strip_tac >>
  `idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  drule_all dse_pending_at_no_read >> strip_tac >>
  irule dse_frame_read_no_clobber >> gvs[]
QED

Theorem dse_local_agrees_frame_read_step:
  dse_frame_read_opcode inst.inst_opcode /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P s1
Proof
  strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  drule_all dse_frame_read_common_update >> strip_tac
  >- (qexists_tac `update_var out w t` >> simp[] >>
      conj_tac
      >- (gvs[] >> irule dse_local_agrees_inst_idx >>
          irule dse_local_agrees_update_var >> simp[]) >>
      irule dse_frame_read_pending_step >> gvs[update_var_def] >> metis_tac[]) >>
  qexists_tac `update_var out w (t with vs_gas_readings := gs)` >> simp[] >>
  conj_tac
  >- (gvs[] >> irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_update_var >>
      irule dse_local_agrees_gas_readings >> simp[]) >>
  irule dse_frame_read_pending_step >> gvs[update_var_def] >> metis_tac[]
QED

(* Unconditional retention by opcode alone is invalid for DLOAD:
   its static MEMORY write effect admits selection. Successful execution
   requires an output, whereas the sound dead-store contract forbids it. *)
Theorem dse_frame_read_success_outputs:
  dse_frame_read_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s1 ==>
  inst.inst_outputs <> []
Proof
  simp[dse_frame_read_opcode_def] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_read0_def, exec_read1_def, exec_gas_def, AllCaseEqs()]
QED

Theorem dse_frame_read_retained:
  wf_function fn /\ all_dead_stores dead_ids cfg aliases bp sp fn /\
  MEM inst (fn_insts fn) /\ dse_frame_read_opcode inst.inst_opcode /\
  step_inst fuel ctx inst s = OK s1 ==>
  dse_inst dead_ids sp inst = inst
Proof
  strip_tac >> drule_all dse_frame_read_success_outputs >> strip_tac >>
  Cases_on `inst.inst_id IN dead_ids` >- (
    drule_all all_dead_stores_occurrence >> strip_tac >> gvs[]) >>
  simp[dse_inst_def]
QED
