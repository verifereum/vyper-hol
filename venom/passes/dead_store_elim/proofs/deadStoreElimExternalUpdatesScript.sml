Theory deadStoreElimExternalUpdates
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimMemory deadStoreElimSafety
  deadStoreElimDefs deadStoreElimStoreSteps deadStoreElimLiveness
  basePtrDefs memLocDefs venomEffects venomInst venomExecSemantics venomState list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

(* All fields adopted from an external outcome, without the separate
 * return-buffer memory write. DELEGATECALL keeps outcomes/requests unchanged. *)
Definition dse_external_update_def:
  dse_external_update accounts ts logs deletions returndata outcomes requests s =
    s with <| vs_accounts := accounts; vs_transient := ts;
              vs_logs := logs; vs_pending_deletions := deletions;
              vs_returndata := returndata; vs_outcomes := outcomes;
              vs_requests := requests |>
End

Theorem dse_external_update_allocas[simp]:
  (dse_external_update accounts ts logs dels rd os rqs s).vs_allocas = s.vs_allocas
Proof
  simp[dse_external_update_def]
QED

Theorem dse_local_agrees_external_update:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory P
    (dse_external_update accounts ts logs dels rd os rqs s)
    (dse_external_update accounts ts logs dels rd os rqs t)
Proof
  simp[dse_external_update_def, dse_local_agrees_def, dse_pending_space_def,
       dse_safety_agrees_def, dse_operational_agrees_def, dse_equiv_def,
       dse_pending_memory_def, dse_memory_byte_def, lookup_var_def]
QED


Theorem dse_segment_unknown_size:
  ops.iao_size = NONE ==> (bp_segment_from_ops bp ops).ml_size = NONE
Proof
  strip_tac >> Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, ml_undefined_def] >>
  CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem dse_external_write_size:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2} ==>
  (bp_get_write_location bp inst AddrSp_Memory).ml_size = NONE \/
  (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME 0
Proof
  simp[] >> strip_tac >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, empty_effects_def, all_effects_def, ml_empty_def] >>
  Cases_on `mem_write_ops inst` >> simp[ml_undefined_def] >>
  disj1_tac >> irule dse_segment_unknown_size >>
  gvs[mem_write_ops_def, AllCaseEqs()]
QED

Theorem dse_external_no_clobber:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2} /\
  loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp AddrSp_Memory loc inst
Proof
  strip_tac >> drule dse_external_write_size >>
  disch_then (qspec_then `bp` strip_assume_tac) >>
  simp[dse_inst_clobbers_def, completely_contains_def]
QED

Theorem dse_external_pending_step:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2} /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx) P s1
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_external_no_clobber >> metis_tac[]
QED

Theorem dse_external_pending_write_step:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2} /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ s1.vs_allocas = s.vs_allocas ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    (FILTER (\(loc,(b,n)). ~(a <= b /\ b+n <= a+LENGTH bytes)) P) s1
Proof
  strip_tac >> irule dse_pending_at_filter >>
  irule dse_external_pending_step >> metis_tac[]
QED
