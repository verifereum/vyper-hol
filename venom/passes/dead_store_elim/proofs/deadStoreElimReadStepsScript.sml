Theory deadStoreElimReadSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLocations
  deadStoreElimLiveness deadStoreElimDefs basePtrDefs memLocDefs
  venomExecSemantics venomState venomEffects venomInst venomMemDefs
  deadStoreElimEquiv list
  deadStoreElimFrame

Theorem dse_load_write_location:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >> Cases_on `sp` >>
  gvs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def,
      empty_effects_def]
QED

Theorem dse_load_no_clobber:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} /\
  loc.ml_size = SOME n /\ 0 < n ==>
  ~dse_inst_clobbers bp sp loc inst
Proof
  strip_tac >> drule dse_load_write_location >>
  disch_then (qspec_then `sp` assume_tac) >>
  simp[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_mload_read_region:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [op] /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  eval_operand op s = SOME w ==>
  dse_region_matches (bp_get_read_location bp inst AddrSp_Memory)
    s (w2n w) 32
Proof
  strip_tac >>
  `bp_get_read_location bp inst AddrSp_Memory =
    bp_segment_from_ops bp
      <|iao_ofst := op; iao_size := SOME (Lit 32w);
        iao_max_size := SOME (Lit 32w)|>` by
    simp[bp_get_read_location_def, is_raw_fmp_opcode_def,
         read_effects_def, mem_read_ops_def] >>
  `w2n (32w:bytes32) = 32` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  simp[] >> irule bp_segment_region_matches >>
  simp[eval_operand_def, Excl "w2n_n2w"] >>
  qexistsl_tac [`inst`, `AddrSp_Memory`] >>
  simp[bp_access_ops_def, mem_read_ops_def]
QED

Theorem dse_key_load_read_region:
  ((inst.inst_opcode = SLOAD /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TLOAD /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [op] /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ eval_operand op s = SOME w ==>
  dse_region_matches (bp_get_read_location bp inst sp) s (w2n w) 1
Proof
  strip_tac >>
  `bp_get_read_location bp inst sp =
    bp_segment_from_ops bp
      <|iao_ofst := op; iao_size := SOME (Lit 1w);
        iao_max_size := SOME (Lit 1w)|>` by
    (gvs[bp_get_read_location_def]) >>
  `w2n (1w:bytes32) = 1` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  simp[] >> irule bp_segment_region_matches >>
  simp[eval_operand_def, Excl "w2n_n2w"] >>
  qexistsl_tac [`inst`, `sp`] >>
  gvs[bp_access_ops_def]
QED

Theorem dse_local_agrees_mload:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [op] /\
  alloca_inv s /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ eval_operand op s = SOME w ==>
  mload (w2n w) s = mload (w2n w) t
Proof
  strip_tac >> Cases_on `sp = AddrSp_Memory`
  >- (fs[] >>
      `dse_region_matches (bp_get_read_location bp inst AddrSp_Memory)
         s (w2n w) 32` by (irule dse_mload_read_region >> metis_tac[]) >>
      `read_memory (w2n w) 32 s = read_memory (w2n w) 32 t` by
        (irule dse_pending_at_read_memory >>
         fs[dse_local_agrees_def, alloca_inv_def] >> metis_tac[]) >>
      fs[mload_def, read_memory_def]) >>
  fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def,
     mload_def]
QED

Theorem dse_pending_at_key_read:
  dse_pending_at cfg bp sp fn bb idx P s /\
  (sp = AddrSp_Storage \/ sp = AddrSp_Transient) /\
  idx < LENGTH bb.bb_instructions /\ allocas_non_overlapping s /\
  dse_region_matches (bp_get_read_location bp (EL idx bb.bb_instructions) sp)
    s (w2n (k:bytes32)) 1 /\ MEM (loc,(a,n)) P ==>
  k <> n2w a
Proof
  strip_tac >>
  `~may_overlap loc (bp_get_read_location bp (EL idx bb.bb_instructions) sp)` by
    (drule_all dse_pending_at_no_read >>
     simp[dse_inst_reads_alias_def, memAliasDefsTheory.ma_may_alias_def] >>
     metis_tac[memLocPropsTheory.may_overlap_sym]) >>
  `regions_disjoint (a,n) (w2n k,1)` by
    (irule dse_pending_at_nonalias >> metis_tac[]) >>
  `key_ok P` by fs[dse_pending_at_def] >>
  fs[key_ok_def, EVERY_MEM] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  strip_tac >> gvs[regions_disjoint_def]
QED

Theorem dse_local_agrees_key_load:
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  ((inst.inst_opcode = SLOAD /\ readsp = AddrSp_Storage) \/
   (inst.inst_opcode = TLOAD /\ readsp = AddrSp_Transient)) /\
  inst.inst_operands = [op] /\ alloca_inv s /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ eval_operand op s = SOME w ==>
  (if readsp = AddrSp_Storage then sload w s else tload w s) =
  (if readsp = AddrSp_Storage then sload w t else tload w t)
Proof
  strip_tac >> (Cases_on `sp = readsp`
  >- (fs[] >>
      `dse_region_matches (bp_get_read_location bp inst readsp) s (w2n w) 1` by
        (irule dse_key_load_read_region >> metis_tac[]) >>
      `!loc a n. MEM (loc,(a,n)) P ==> w <> n2w a` by
        (rpt gen_tac >> disch_tac >> irule dse_pending_at_key_read >>
         fs[alloca_inv_def] >> metis_tac[]) >>
      `key_ok P` by fs[dse_pending_at_def] >>
      fs[dse_local_agrees_def] >>
      Cases_on `readsp = AddrSp_Storage` >> fs[] >>
      metis_tac[dse_pending_space_sload, dse_pending_space_tload]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (irule dse_equiv_call_ctx >>
     fs[dse_local_agrees_def, dse_pending_space_def] >> metis_tac[]) >>
  fs[dse_local_agrees_def, dse_pending_space_def] >>
  Cases_on `readsp = AddrSp_Storage` >>
  fs[dse_equiv_def, sload_def, tload_def,
     contract_storage_def, contract_transient_def] >> metis_tac[])
QED

Theorem dse_load_step:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} ==>
  step_inst fuel ctx inst s =
    exec_read1
      (if inst.inst_opcode = MLOAD then (\w s. mload (w2n w) s)
       else if inst.inst_opcode = SLOAD then sload else tload) inst s
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, SF ETA_ss]
QED

Theorem dse_load_ok_shape:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?op w out.
    inst.inst_operands = [op] /\ eval_operand op s = SOME w /\
    inst.inst_outputs = [out] /\
    s1 = update_var out
      (if inst.inst_opcode = MLOAD then mload (w2n w) s
       else if inst.inst_opcode = SLOAD then sload w s else tload w s) s
Proof
  strip_tac >> drule dse_load_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> gvs[exec_read1_def, AllCaseEqs()] >>
  Cases_on `inst.inst_opcode = MLOAD` >>
  Cases_on `inst.inst_opcode = SLOAD` >> gvs[] >> metis_tac[]
QED

Theorem dse_load_pending_step:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P (update_var out w s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[update_var_def] >>
  irule dse_pending_at_step >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  irule dse_load_no_clobber >> metis_tac[]
QED

Theorem dse_local_agrees_load_value:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  inst.inst_operands = [op] /\ alloca_inv s /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ eval_operand op s = SOME w ==>
  (if inst.inst_opcode = MLOAD then mload (w2n w) s
   else if inst.inst_opcode = SLOAD then sload w s else tload w s) =
  (if inst.inst_opcode = MLOAD then mload (w2n w) t
   else if inst.inst_opcode = SLOAD then sload w t else tload w t)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = MLOAD`
  >- (simp[] >> irule dse_local_agrees_mload >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = SLOAD` >> simp[]
  >- (drule dse_local_agrees_key_load >>
      disch_then (qspecl_then [`w`, `AddrSp_Storage`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  `inst.inst_opcode = TLOAD` by fs[] >>
  drule dse_local_agrees_key_load >>
  disch_then (qspecl_then [`w`, `AddrSp_Transient`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem dse_local_agrees_load_step:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  alloca_inv s /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P s1
Proof
  strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_load_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[deadStoreElimSafetyTheory.dse_safety_agrees_eval_operand]) >>
  `eval_operand op t = SOME w` by metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  drule_all dse_local_agrees_load_value >> strip_tac >>
  qexists_tac `update_var out
    (if inst.inst_opcode = MLOAD then mload (w2n w) t
     else if inst.inst_opcode = SLOAD then sload w t else tload w t) t` >>
  conj_tac
  >- (drule dse_load_step >>
      disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >>
      simp[exec_read1_def] >>
      Cases_on `inst.inst_opcode = MLOAD` >>
      Cases_on `inst.inst_opcode = SLOAD` >> simp[]) >>
  conj_tac
  >- (gvs[] >> irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_update_var >> simp[]) >>
  gvs[] >> irule dse_load_pending_step >> simp[] >> metis_tac[]
QED

Theorem dse_load_result_cases:
  inst.inst_opcode IN {MLOAD; SLOAD; TLOAD} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> drule dse_load_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] SUBST1_TAC) >>
  namedCases_on `inst.inst_operands` ["", "operand ops"]
  >- simp[exec_read1_def] >>
  Cases_on `ops`
  >- (Cases_on `eval_operand operand s` >> simp[exec_read1_def] >>
      namedCases_on `inst.inst_outputs` ["", "output outputs"]
      >- simp[] >>
      Cases_on `outputs` >> simp[]) >>
  rename1 `inst.inst_operands = operand::operand2::ops2` >>
  Cases_on `ops2` >> simp[exec_read1_def]
QED
