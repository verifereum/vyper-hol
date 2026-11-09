Theory deadStoreElimImmutableSteps
Ancestors
  deadStoreElimStoreSteps deadStoreElimLocal deadStoreElimPending
  deadStoreElimLiveness deadStoreElimSafety deadStoreElimEquiv deadStoreElimMemory
  deadStoreElimDefs deadStoreElimFrame deadStoreElimStructure venomExecSemantics venomState
  venomMemDefs venomMemProps venomEffects venomInst basePtrDefs memLocDefs list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_local_agrees_immutables:
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (s with vs_immutables := im)
    (t with vs_immutables := im)
Proof
  simp[dse_local_agrees_def, dse_pending_space_def,
       dse_safety_agrees_def, dse_operational_agrees_def,
       dse_equiv_def, lookup_var_def, dse_pending_memory_def,
       dse_pending_keys_def, dse_memory_byte_def] >> rpt strip_tac >> gvs[]
QED

Theorem dse_local_agrees_istore_memory:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory
    (FILTER (\(loc,(b,m)). ~(a <= b /\ b+m <= a+32)) P)
    (istore a v s) (istore a v t)
Proof
  strip_tac >>
  `s.vs_immutables = t.vs_immutables` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  simp[istore_def, mstore_eq_write_mem] >>
  irule dse_local_agrees_immutables >>
  drule dse_local_agrees_memory_overwrite >>
  disch_then (qspecl_then [`word_to_bytes v T`, `a`] mp_tac) >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem dse_istore_pending_memory_step:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\ inst.inst_opcode = ISTORE /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME a /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+32)) P)
    (istore (w2n a) v s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[istore_def, mstore_def] >>
  irule (SRULE [] dse_pending_at_overwrite_step) >> simp[] >>
  rpt strip_tac >>
  `inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE}` by simp[] >>
  drule_all dse_mstore_clobber_covered >> simp[]
QED

Theorem dse_istore_step:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [addr; value] ==>
  step_inst fuel ctx inst s = exec_write2 (\a v s. istore (w2n a) v s) inst s
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_write2_def] >>
  Cases_on `eval_operand addr s` >> simp[] >>
  Cases_on `eval_operand value s` >> simp[]
QED

Theorem dse_istore_ok_shape:
  inst.inst_opcode = ISTORE /\ step_inst fuel ctx inst s = OK s1 ==>
  ?addr value a v.
    inst.inst_operands = [addr; value] /\
    eval_operand addr s = SOME a /\ eval_operand value s = SOME v /\
    s1 = istore (w2n a) v s
Proof
  strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem dse_local_agrees_istore_memory_step:
  inst.inst_opcode = ISTORE /\ dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees AddrSp_Memory P1
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp AddrSp_Memory fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_istore_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand addr t = SOME a /\ eval_operand value t = SOME v` by metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexistsl_tac [
    `FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+32)) P`,
    `istore (w2n a) v t`] >>
  conj_tac
  >- simp[dse_istore_step, exec_write2_def] >>
  conj_tac
  >- (gvs[] >> irule dse_local_agrees_inst_idx >>
      irule (SRULE [] dse_local_agrees_istore_memory) >> simp[]) >>
  gvs[] >> irule (SRULE [] dse_istore_pending_memory_step) >> metis_tac[]
QED

Theorem dse_local_agrees_istore_other:
  sp <> AddrSp_Memory /\ dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (istore a v s) (istore a v t)
Proof
  strip_tac >>
  `s.vs_immutables = t.vs_immutables` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  simp[istore_def, mstore_eq_write_mem] >>
  irule dse_local_agrees_immutables >>
  irule dse_local_agrees_other_memory_write >> simp[]
QED

Theorem dse_istore_other_pending_step:
  inst.inst_opcode = ISTORE /\ sp <> AddrSp_Memory /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P (istore a v s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[istore_def, mstore_def] >>
  irule dse_pending_at_step >> simp[] >> rpt strip_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  `inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE}` by simp[] >>
  drule_all dse_mstore_other_write_location >>
  disch_then (qspec_then `bp` assume_tac) >>
  fs[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_local_agrees_istore_other_step:
  inst.inst_opcode = ISTORE /\ sp <> AddrSp_Memory /\
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
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_istore_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand addr t = SOME a /\ eval_operand value t = SOME v` by metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexists_tac `istore (w2n a) v t` >>
  conj_tac >- simp[dse_istore_step, exec_write2_def] >>
  conj_tac
  >- (gvs[] >> irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_istore_other >> simp[]) >>
  gvs[] >> irule dse_istore_other_pending_step >> metis_tac[]
QED

Theorem dse_local_agrees_istore_step:
  inst.inst_opcode = ISTORE /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >> Cases_on `sp = AddrSp_Memory`
  >- (gvs[] >> drule_all dse_local_agrees_istore_memory_step >> simp[]) >>
  drule_all dse_local_agrees_istore_other_step >> metis_tac[]
QED

Theorem dse_istore_result_cases:
  inst.inst_opcode = ISTORE ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >- simp[] >>
  namedCases_on `ops` ["", "op2 ops2"] >- simp[] >>
  Cases_on `ops2` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[] >>
  Cases_on `eval_operand op2 s` >> simp[]
QED

Theorem dse_istore_retained:
  wf_function fn /\ all_dead_stores ids cfg aliases bp sp fn /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ISTORE ==>
  dse_inst ids sp inst = inst
Proof
  strip_tac >> Cases_on `inst.inst_id IN ids`
  >- (drule_all all_dead_stores_occurrence >> strip_tac >>
      Cases_on `sp` >>
      gvs[effects_in_space_def, is_memory_def_opcode_def, write_effects_def]) >>
  simp[dse_inst_def]
QED
