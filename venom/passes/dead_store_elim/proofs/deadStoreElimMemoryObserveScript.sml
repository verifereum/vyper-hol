Theory deadStoreElimMemoryObserve
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLocations
  deadStoreElimOpcodeCoverage deadStoreElimDefs basePtrDefs memLocDefs
  venomState venomMemDefs list

Theorem dse_precise_input_bytes:
  inst.inst_opcode IN {CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
    RETURN; REVERT; SHA3; LOG} /\
  mem_read_ops inst = SOME ops /\ ops.iao_size = SOME sizeop /\
  ops.iao_max_size = SOME sizeop /\
  eval_operand ops.iao_ofst s = SOME off /\
  eval_operand sizeop s = SOME sz /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst ==>
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t
Proof
  strip_tac >>
  `bp_access_ops AddrSp_Memory inst ops` by simp[bp_access_ops_def] >>
  `dse_region_matches (bp_segment_from_ops bp ops) s (w2n off) (w2n sz)` by
    (irule bp_segment_region_matches >>
     rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]) >>
  drule dse_precise_memory_read_location >>
  disch_then (qspec_then `bp` assume_tac) >>
  irule dse_pending_at_read_memory >>
  rpt (goal_assum (drule_at Any)) >>
  gvs[dse_local_agrees_def]
QED

Theorem dse_sha3_input_bytes:
  inst.inst_opcode = SHA3 /\ inst.inst_operands = [offsetop; sizeop] /\
  eval_operand offsetop s = SOME off /\ eval_operand sizeop s = SOME sz /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst ==>
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t
Proof
  strip_tac >> irule dse_precise_input_bytes >>
  rpt (goal_assum (drule_at Any)) >>
  simp[mem_read_ops_def] >> metis_tac[]
QED

Theorem dse_log_read_ops:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: rest /\
  LENGTH rest = w2n tc + 2 ==>
  mem_read_ops inst = SOME <| iao_ofst := EL 0 (REVERSE rest);
    iao_size := SOME (EL 1 (REVERSE rest));
    iao_max_size := SOME (EL 1 (REVERSE rest)) |>
Proof
  strip_tac >>
  `2 <= LENGTH (REVERSE rest)` by simp[] >>
  namedCases_on `REVERSE rest` ["", "offsetop tailops"] >> gvs[] >>
  namedCases_on `tailops` ["", "sizeop remaining"] >> gvs[] >>
  Cases_on `remaining` >>
  simp[mem_read_ops_def, REVERSE_DEF]
QED

Theorem dse_log_input_bytes:
  inst.inst_opcode = LOG /\ inst.inst_operands = Lit tc :: rest /\
  LENGTH rest = w2n tc + 2 /\
  eval_operand (EL 0 (REVERSE rest)) s = SOME off /\
  eval_operand (EL 1 (REVERSE rest)) s = SOME sz /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  allocas_non_overlapping s /\ dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst ==>
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off) (w2n sz) t
Proof
  strip_tac >> drule_all dse_log_read_ops >> strip_tac >> fs[] >>
  irule dse_precise_input_bytes >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED
