Theory deadStoreElimCopySteps
Ancestors
  deadStoreElimStoreSteps deadStoreElimReadSteps
  deadStoreElimLocal deadStoreElimPending deadStoreElimLocations
  deadStoreElimLiveness deadStoreElimSafety deadStoreElimDefs
  deadStoreElimEquiv venomExecSemantics venomState venomMemDefs
  venomMemProps venomEffects venomInst basePtrDefs memLocDefs list
  deadStoreElimFrame
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_mcopy_step:
  inst.inst_opcode = MCOPY ==>
  step_inst fuel ctx inst s =
    case inst.inst_operands of
      [op_dst; src; szop] =>
        (case (eval_operand op_dst s, eval_operand src s, eval_operand szop s) of
           (SOME a, SOME b, SOME n) =>
             OK (write_memory_with_expansion (w2n a)
                   (read_memory (w2n b) (w2n n) s) s)
         | _ => Error "undefined operand")
    | _ => Error "mcopy requires 3 operands"
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, mcopy_def, read_memory_def]
QED

Theorem dse_mcopy_ok_shape:
  inst.inst_opcode = MCOPY /\ step_inst fuel ctx inst s = OK s1 ==>
  ?op_dst src szop a b n.
    inst.inst_operands = [op_dst; src; szop] /\
    eval_operand op_dst s = SOME a /\ eval_operand src s = SOME b /\
    eval_operand szop s = SOME n /\
    s1 = write_memory_with_expansion (w2n a)
           (read_memory (w2n b) (w2n n) s) s
Proof
  strip_tac >> drule dse_mcopy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem dse_copy_write_location:
  ((inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY} /\
    inst.inst_operands = [op_dst; src; szop]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    ?addr. inst.inst_operands = [addr; op_dst; src; szop])) ==>
  bp_get_write_location bp inst AddrSp_Memory =
    bp_segment_from_ops bp
      <|iao_ofst := op_dst; iao_size := SOME szop; iao_max_size := SOME szop|>
Proof
  simp[] >> strip_tac >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, mem_write_ops_def]
QED

Theorem dse_mcopy_read_region:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [op_dst; src; szop] /\
  eval_operand src s = SOME b /\ eval_operand szop s = SOME n /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
  dse_region_matches (bp_get_read_location bp inst AddrSp_Memory)
    s (w2n b) (w2n n)
Proof
  strip_tac >>
  simp[bp_get_read_location_def, is_raw_fmp_opcode_def,
       read_effects_def, mem_read_ops_def] >>
  irule bp_segment_region_matches >> simp[] >>
  qexistsl_tac [`inst`, `AddrSp_Memory`] >>
  simp[bp_access_ops_def, mem_read_ops_def]
QED

Theorem dse_copy_write_region:
  ((inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY} /\
    inst.inst_operands = [op_dst; src; szop]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    ?addr. inst.inst_operands = [addr; op_dst; src; szop])) /\
  eval_operand op_dst s = SOME a /\ eval_operand szop s = SOME n /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
  dse_region_matches (bp_get_write_location bp inst AddrSp_Memory)
    s (w2n a) (w2n n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dse_copy_write_location >>
  disch_then (qspec_then `bp` SUBST1_TAC) >>
  irule bp_segment_region_matches >> simp[] >>
  qexistsl_tac [`inst`, `AddrSp_Memory`] >>
  fs[bp_access_ops_def, mem_write_ops_def]
QED

Theorem dse_copy_write_size:
  ((inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY} /\
    inst.inst_operands = [op_dst; src; szop]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    ?addr. inst.inst_operands = [addr; op_dst; src; szop])) /\
  eval_operand szop s = SOME n /\
  (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME k ==>
  k = w2n n
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dse_copy_write_location >>
  disch_then (qspec_then `bp` assume_tac) >> gvs[] >>
  drule bp_segment_size_eval >> simp[] >> metis_tac[]
QED

Theorem dse_mcopy_snapshot:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [op_dst; src; szop] /\
  eval_operand src s = SOME b /\ eval_operand szop s = SOME n /\
  dse_local_agrees sp P s t /\ dse_pending_at cfg bp sp fn bb idx P s /\
  idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = inst /\
  alloca_inv s /\ bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
  read_memory (w2n b) (w2n n) s = read_memory (w2n b) (w2n n) t
Proof
  strip_tac >> Cases_on `sp = AddrSp_Memory`
  >- (fs[] >>
      `dse_region_matches (bp_get_read_location bp inst AddrSp_Memory)
         s (w2n b) (w2n n)` by (irule dse_mcopy_read_region >> metis_tac[]) >>
      irule dse_pending_at_read_memory >>
      fs[dse_local_agrees_def, alloca_inv_def] >> metis_tac[]) >>
  fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def, read_memory_def]
QED

Theorem dse_copy_clobber_covered:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  ((inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY} /\
    inst.inst_operands = [op_dst; src; szop]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    ?addr. inst.inst_operands = [addr; op_dst; src; szop])) /\
  eval_operand op_dst s = SOME a /\ eval_operand szop s = SOME n /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  MEM (loc,(b,m)) P /\ dse_inst_clobbers bp AddrSp_Memory loc inst ==>
  w2n a <= b /\ b+m <= w2n a + w2n n
Proof
  strip_tac >> drule_all dse_pending_at_member >> strip_tac >>
  `?k. (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME k` by
    (fs[dse_inst_clobbers_def, completely_contains_def] >>
     Cases_on `(bp_get_write_location bp inst AddrSp_Memory).ml_size` >> fs[]) >>
  `dse_region_matches (bp_get_write_location bp inst AddrSp_Memory)
    s (w2n a) (w2n n)` by (irule dse_copy_write_region >> metis_tac[]) >>
  `k = w2n n` by (irule dse_copy_write_size >> metis_tac[]) >> gvs[] >>
  drule_all dse_pending_at_clobber_covered >> simp[]
QED

Theorem dse_copy_pending_memory_step:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  ((inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY} /\
    inst.inst_operands = [op_dst; src; szop]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    ?addr. inst.inst_operands = [addr; op_dst; src; szop])) /\
  eval_operand op_dst s = SOME a /\ eval_operand szop s = SOME n /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  LENGTH bytes = w2n n ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P)
    (write_memory_with_expansion (w2n a) bytes s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[write_memory_with_expansion_def] >>
  irule (SRULE [] dse_pending_at_overwrite_step) >> simp[] >>
  rpt strip_tac >> metis_tac[dse_copy_clobber_covered]
QED

Theorem dse_local_agrees_mcopy_memory_step:
  inst.inst_opcode = MCOPY /\ dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ alloca_inv s /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees AddrSp_Memory P1
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp AddrSp_Memory fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_mcopy_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand op_dst t = SOME a /\ eval_operand src t = SOME b /\
   eval_operand szop t = SOME n` by metis_tac[] >>
  `read_memory (w2n b) (w2n n) s = read_memory (w2n b) (w2n n) t` by
    (irule dse_mcopy_snapshot >> metis_tac[]) >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexistsl_tac [
    `FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+w2n n)) P`,
    `write_memory_with_expansion (w2n a) (read_memory (w2n b) (w2n n) s) t`] >>
  conj_tac
  >- (drule dse_mcopy_step >>
      disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      qmatch_goalsub_abbrev_tac `write_memory_with_expansion _ bytes _` >>
      `w2n n = LENGTH bytes` by simp[Abbr `bytes`, read_memory_def, LENGTH_TAKE_EQ] >>
      pop_assum SUBST1_TAC >>
      irule dse_local_agrees_memory_overwrite >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  qmatch_goalsub_abbrev_tac `write_memory_with_expansion _ bytes _` >>
  `w2n n = LENGTH bytes` by simp[Abbr `bytes`, read_memory_def, LENGTH_TAKE_EQ] >>
  pop_assum SUBST1_TAC >>
  irule dse_copy_pending_memory_step >>
  simp[read_memory_def, LENGTH_TAKE_EQ] >> metis_tac[]
QED

Theorem dse_copy_pending_insert_step:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  ((inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY} /\
    inst.inst_operands = [op_dst; src; szop]) \/
   (inst.inst_opcode = EXTCODECOPY /\
    ?addr. inst.inst_operands = [addr; op_dst; src; szop])) /\
  eval_operand op_dst s = SOME a /\ eval_operand szop s = SOME n /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  LENGTH bytes = w2n n /\
  (bp_get_write_location bp inst AddrSp_Memory).ml_size <> SOME 0 /\
  ml_is_fixed (bp_get_write_location bp inst AddrSp_Memory) /\
  dse_suffix_dead cfg FEMPTY bp (bp_get_write_location bp inst AddrSp_Memory)
    AddrSp_Memory fn bb (SUC idx) ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    ((bp_get_write_location bp inst AddrSp_Memory,(w2n a,LENGTH bytes))::
      FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P)
    (write_memory_with_expansion (w2n a) bytes s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[write_memory_with_expansion_def] >>
  irule dse_pending_at_cons >> simp[] >>
  `?k. (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME k` by
    (fs[ml_is_fixed_def] >>
     Cases_on `(bp_get_write_location bp inst AddrSp_Memory).ml_size` >> fs[]) >>
  `k = w2n n` by (irule dse_copy_write_size >> metis_tac[]) >>
  `dse_region_matches (bp_get_write_location bp inst AddrSp_Memory)
    s (w2n a) (w2n n)` by (irule dse_copy_write_region >> metis_tac[]) >>
  `dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P) s` by
    (pure_rewrite_tac [DE_MORGAN_THM] >>
     irule (SRULE [] dse_pending_at_overwrite_step) >> simp[] >>
     rpt strip_tac >> metis_tac[dse_copy_clobber_covered]) >>
  gvs[arithmeticTheory.ADD_COMM] >>
  spose_not_then assume_tac >> `w2n n = 0` by decide_tac >> fs[]
QED

Theorem dse_local_agrees_mcopy_deleted_step:
  inst.inst_opcode = MCOPY /\ inst.inst_outputs = [] /\
  dse_local_agrees AddrSp_Memory P s t /\
  dse_pending_at cfg bp AddrSp_Memory fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  ml_is_fixed (bp_get_write_location bp inst AddrSp_Memory) /\
  (bp_get_write_location bp inst AddrSp_Memory).ml_size <> SOME 0 /\
  dse_suffix_dead cfg FEMPTY bp (bp_get_write_location bp inst AddrSp_Memory)
    AddrSp_Memory fn bb (SUC s.vs_inst_idx) /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?P1. dse_local_agrees AddrSp_Memory P1
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp AddrSp_Memory fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_mcopy_ok_shape >> strip_tac >>
  qmatch_asmsub_abbrev_tac `s1 = write_memory_with_expansion _ bytes _` >>
  `LENGTH bytes = w2n n` by simp[Abbr `bytes`, read_memory_def, LENGTH_TAKE_EQ] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexists_tac `(bp_get_write_location bp inst AddrSp_Memory,(w2n a,LENGTH bytes))::
    FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P` >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_memory_insert_cover >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_copy_pending_insert_step >> simp[] >> metis_tac[]
QED

Theorem dse_copy_other_write_location:
  inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY} /\
  sp <> AddrSp_Memory ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  strip_tac >> Cases_on `sp` >>
  fs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def]
QED

Theorem dse_copy_other_pending_step:
  inst.inst_opcode IN {MCOPY; CALLDATACOPY; CODECOPY; DLOADBYTES; RETURNDATACOPY; EXTCODECOPY} /\
  sp <> AddrSp_Memory /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P
    (write_memory_with_expansion a bytes s)
Proof
  strip_tac >> irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[write_memory_with_expansion_def] >>
  irule dse_pending_at_step >> simp[] >> rpt strip_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  drule_all dse_copy_other_write_location >>
  disch_then (qspec_then `bp` assume_tac) >>
  fs[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_local_agrees_mcopy_other_step:
  inst.inst_opcode = MCOPY /\ sp <> AddrSp_Memory /\
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
  drule_all dse_mcopy_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand op_dst t = SOME a /\ eval_operand src t = SOME b /\
   eval_operand szop t = SOME n` by metis_tac[] >>
  `read_memory (w2n b) (w2n n) s = read_memory (w2n b) (w2n n) t` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def, read_memory_def] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexists_tac `write_memory_with_expansion (w2n a)
    (read_memory (w2n b) (w2n n) s) t` >>
  conj_tac
  >- (drule dse_mcopy_step >>
      disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_other_memory_write >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_copy_other_pending_step >> fs[]
QED

Theorem dse_local_agrees_mcopy_step:
  inst.inst_opcode = MCOPY /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  alloca_inv s /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >> Cases_on `sp = AddrSp_Memory`
  >- (qpat_x_assum `sp = AddrSp_Memory` SUBST_ALL_TAC >>
      drule_all dse_local_agrees_mcopy_memory_step >> simp[]) >>
  drule_all dse_local_agrees_mcopy_other_step >> metis_tac[]
QED

Theorem dse_mcopy_result_cases:
  inst.inst_opcode = MCOPY ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> drule dse_mcopy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] SUBST1_TAC) >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >- simp[] >>
  namedCases_on `ops` ["", "op2 ops2"] >- simp[] >>
  namedCases_on `ops2` ["", "op3 ops3"] >- simp[] >>
  Cases_on `ops3` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[] >>
  Cases_on `eval_operand op2 s` >> simp[] >>
  Cases_on `eval_operand op3 s` >> simp[]
QED
