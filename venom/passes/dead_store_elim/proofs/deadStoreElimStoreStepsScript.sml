Theory deadStoreElimStoreSteps
Ancestors
  deadStoreElimLocal deadStoreElimPending deadStoreElimLocations
  deadStoreElimMemory deadStoreElimLiveness deadStoreElimSafety
  deadStoreElimEquiv deadStoreElimDefs deadStoreElimFrame
  venomExecSemantics venomState venomMemDefs venomMemProps
  venomEffects venomInst basePtrDefs memLocDefs list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_footprints_filter:
  MAP SND (FILTER (\(loc,(b,n)). ~((a:num) <= b /\ b+n <= a+k)) P) =
  FILTER (\(b,n). ~(a <= b /\ b+n <= a+k)) (MAP SND P)
Proof
  Induct_on `P` >- simp[] >>
  gen_tac >> PairCases_on `h` >> simp[] >> IF_CASES_TAC >> gvs[]
QED

Theorem dse_local_agrees_memory_overwrite:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory
    (FILTER (\(loc,(b,n)). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
    (write_memory_with_expansion a bytes s)
    (write_memory_with_expansion a bytes t)
Proof
  strip_tac >>
  `dse_pending_memory (MAP SND P) s t` by
    fs[dse_local_agrees_def, dse_pending_space_def] >>
  drule dse_pending_memory_overwrite >>
  disch_then (qspecl_then [`bytes`, `a`] assume_tac) >>
  rewrite_tac[dse_local_agrees_def, dse_pending_space_def,
              dse_footprints_filter] >>
  fs[dse_local_agrees_def, dse_pending_space_def,
     SRULE [] dse_footprints_filter, dse_safety_agrees_def,
     dse_operational_agrees_def, dse_equiv_def,
     write_memory_with_expansion_def, lookup_var_def]
QED

Theorem dse_local_agrees_memory_insert_cover:
  dse_local_agrees AddrSp_Memory P s t ==>
  dse_local_agrees AddrSp_Memory
    ((loc,(a,LENGTH bytes))::
      FILTER (\(loc,(b,n)). ~(a <= b /\ b+n <= a+LENGTH bytes)) P)
    (write_memory_with_expansion a bytes s) t
Proof
  strip_tac >>
  `dse_pending_memory (MAP SND P) s t` by
    fs[dse_local_agrees_def, dse_pending_space_def] >>
  drule dse_pending_memory_insert_cover >>
  disch_then (qspecl_then [`bytes`, `a`] assume_tac) >>
  rewrite_tac[dse_local_agrees_def, dse_pending_space_def,
              dse_footprints_filter] >>
  fs[dse_local_agrees_def, dse_pending_space_def,
     SRULE [] dse_footprints_filter, dse_safety_agrees_def,
     dse_operational_agrees_def, dse_equiv_def,
     write_memory_with_expansion_def, lookup_var_def]
QED

Theorem dse_local_agrees_other_memory_write:
  sp <> AddrSp_Memory /\ dse_local_agrees sp P s t ==>
  dse_local_agrees sp P (write_memory_with_expansion a bytes s)
    (write_memory_with_expansion a bytes t)
Proof
  strip_tac >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
     dse_safety_agrees_def, dse_operational_agrees_def,
     dse_equiv_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem dse_mstore_step:
  inst.inst_opcode IN {MSTORE; MSTORE8} ==>
  step_inst fuel ctx inst s =
    exec_write2 (\a v s.
      write_memory_with_expansion (w2n a)
        (if inst.inst_opcode = MSTORE then word_to_bytes v T
         else [w2w v]) s) inst s
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       lambdify mstore_eq_write_mem, lambdify mstore8_eq_write_mem, SF ETA_ss]
QED

Theorem dse_mstore_ok_shape:
  inst.inst_opcode IN {MSTORE; MSTORE8} /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?addr value a v bytes.
    inst.inst_operands = [addr; value] /\
    eval_operand addr s = SOME a /\ eval_operand value s = SOME v /\
    bytes = (if inst.inst_opcode = MSTORE then word_to_bytes v T
             else [w2w v]) /\
    s1 = write_memory_with_expansion (w2n a) bytes s
Proof
  strip_tac >> drule dse_mstore_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> gvs[exec_write2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem dse_mstore_write_location:
  inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE} /\
  inst.inst_operands = [addr; value] ==>
  bp_get_write_location bp inst AddrSp_Memory =
    bp_segment_from_ops bp
      <|iao_ofst := addr;
        iao_size := SOME (Lit (if inst.inst_opcode = MSTORE8 then 1w else 32w));
        iao_max_size := SOME (Lit (if inst.inst_opcode = MSTORE8 then 1w else 32w))|>
Proof
  simp[] >> strip_tac >>
  simp[bp_get_write_location_def, is_raw_fmp_opcode_def,
       write_effects_def, mem_write_ops_def]
QED

Theorem dse_mstore_write_region:
  inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE} /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME a /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
  dse_region_matches (bp_get_write_location bp inst AddrSp_Memory) s
    (w2n a) (if inst.inst_opcode = MSTORE8 then 1 else 32)
Proof
  strip_tac >> drule_all dse_mstore_write_location >>
  disch_then (qspec_then `bp` SUBST1_TAC) >>
  `w2n (32w:bytes32) = 32 /\ w2n (1w:bytes32) = 1` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  Cases_on `inst.inst_opcode = MSTORE8` >> fs[Excl "w2n_n2w"] >>
  irule bp_segment_region_matches >> simp[eval_operand_def, Excl "w2n_n2w"] >>
  qexistsl_tac [`inst`, `AddrSp_Memory`] >>
  simp[bp_access_ops_def, mem_write_ops_def]
QED

Theorem dse_mstore_write_size:
  inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE} /\
  inst.inst_operands = [addr; value] /\
  (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME n ==>
  n = (if inst.inst_opcode = MSTORE8 then 1 else 32)
Proof
  strip_tac >> drule_all dse_mstore_write_location >>
  disch_then (qspec_then `bp` assume_tac) >> gvs[] >>
  drule bp_segment_size_eval >>
  simp[eval_operand_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Theorem dse_mstore_clobber_covered:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE} /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME a /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  MEM (loc,(b,m)) P /\ dse_inst_clobbers bp AddrSp_Memory loc inst ==>
  w2n a <= b /\ b+m <= w2n a + (if inst.inst_opcode = MSTORE8 then 1 else 32)
Proof
  strip_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  `?n. (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME n` by
    (fs[dse_inst_clobbers_def, completely_contains_def] >>
     Cases_on `(bp_get_write_location bp inst AddrSp_Memory).ml_size` >> fs[]) >>
  drule_all dse_mstore_write_region >> strip_tac >>
  drule_all dse_mstore_write_size >> strip_tac >> gvs[] >>
  drule_all dse_pending_at_clobber_covered >> simp[]
QED

Theorem dse_mstore_pending_memory_step:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  inst.inst_opcode IN {MSTORE; MSTORE8} /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME a /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  LENGTH bytes = (if inst.inst_opcode = MSTORE then 32 else 1) ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P)
    (write_memory_with_expansion (w2n a) bytes s)
Proof
  strip_tac >>
  `inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE}` by fs[] >>
  `((if inst.inst_opcode = MSTORE8 then 1 else 32):num) =
   (if inst.inst_opcode = MSTORE then 32 else 1)` by gvs[] >>
  irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[write_memory_with_expansion_def] >>
  irule (SRULE [] dse_pending_at_overwrite_step) >> simp[] >>
  rpt strip_tac >> drule_all dse_mstore_clobber_covered >> simp[]
QED

Theorem dse_mstore_bytes_length:
  LENGTH (if inst.inst_opcode = MSTORE then word_to_bytes (v:bytes32) T
          else [w2w v : word8]) =
  (if inst.inst_opcode = MSTORE then 32 else 1)
Proof
  Cases_on `inst.inst_opcode = MSTORE` >> simp[byteTheory.LENGTH_word_to_bytes] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Theorem dse_local_agrees_mstore_memory_step:
  inst.inst_opcode IN {MSTORE; MSTORE8} /\
  dse_local_agrees AddrSp_Memory P s t /\
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
  drule_all dse_mstore_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >>
     metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand addr t = SOME a /\ eval_operand value t = SOME v` by
    metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexistsl_tac [
    `FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P`,
    `write_memory_with_expansion (w2n a) bytes t`] >>
  conj_tac
  >- (drule dse_mstore_step >>
      disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >>
      simp[exec_write2_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_memory_overwrite >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_mstore_pending_memory_step >>
  fs[dse_mstore_bytes_length] >> metis_tac[]
QED

Theorem dse_mstore_pending_insert_step:
  dse_pending_at cfg bp AddrSp_Memory fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  inst.inst_opcode IN {MSTORE; MSTORE8} /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME a /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  LENGTH bytes = (if inst.inst_opcode = MSTORE then 32 else 1) /\
  ml_is_fixed (bp_get_write_location bp inst AddrSp_Memory) /\
  dse_suffix_dead cfg FEMPTY bp (bp_get_write_location bp inst AddrSp_Memory)
    AddrSp_Memory fn bb (SUC idx) ==>
  dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    ((bp_get_write_location bp inst AddrSp_Memory,(w2n a,LENGTH bytes))::
      FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P)
    (write_memory_with_expansion (w2n a) bytes s)
Proof
  strip_tac >>
  `inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE}` by fs[] >>
  `((if inst.inst_opcode = MSTORE8 then 1 else 32):num) =
   (if inst.inst_opcode = MSTORE then 32 else 1)` by gvs[] >>
  irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[write_memory_with_expansion_def] >>
  irule dse_pending_at_cons >> simp[] >>
  `?n. (bp_get_write_location bp inst AddrSp_Memory).ml_size = SOME n` by
    (fs[ml_is_fixed_def] >>
     Cases_on `(bp_get_write_location bp inst AddrSp_Memory).ml_size` >> fs[]) >>
  drule_all dse_mstore_write_size >> strip_tac >>
  drule_all dse_mstore_write_region >> strip_tac >>
  `dse_pending_at cfg bp AddrSp_Memory fn bb (SUC idx)
    (FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P) s` by
    (pure_rewrite_tac [DE_MORGAN_THM] >>
     irule (SRULE [] dse_pending_at_overwrite_step) >> simp[] >>
     rpt strip_tac >> drule_all dse_mstore_clobber_covered >> simp[]) >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem dse_local_agrees_mstore_deleted_step:
  inst.inst_opcode IN {MSTORE; MSTORE8} /\
  inst.inst_outputs = [] /\
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
  drule_all dse_mstore_ok_shape >> strip_tac >>
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
  irule dse_mstore_pending_insert_step >>
  fs[dse_mstore_bytes_length] >> metis_tac[]
QED

Theorem dse_mstore_other_write_location:
  inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE} /\ sp <> AddrSp_Memory ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  simp[] >> strip_tac >>
  Cases_on `sp` >>
  fs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def]
QED

Theorem dse_mstore_other_pending_step:
  inst.inst_opcode IN {MSTORE; MSTORE8; ISTORE} /\ sp <> AddrSp_Memory /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P
    (write_memory_with_expansion a bytes s)
Proof
  strip_tac >>
  irule dse_pending_at_allocas_extend >>
  qexists_tac `s` >> simp[write_memory_with_expansion_def] >>
  irule dse_pending_at_step >> simp[] >> rpt strip_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  drule_all dse_mstore_other_write_location >>
  disch_then (qspec_then `bp` assume_tac) >>
  fs[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_local_agrees_mstore_other_step:
  inst.inst_opcode IN {MSTORE; MSTORE8} /\ sp <> AddrSp_Memory /\
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
  drule_all dse_mstore_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand addr t = SOME a /\ eval_operand value t = SOME v` by metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexists_tac `write_memory_with_expansion (w2n a) bytes t` >>
  conj_tac
  >- (drule dse_mstore_step >>
      disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >>
      simp[exec_write2_def]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_other_memory_write >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_mstore_other_pending_step >> fs[]
QED

Theorem dse_local_agrees_mstore_step:
  inst.inst_opcode IN {MSTORE; MSTORE8} /\
  dse_local_agrees sp P s t /\
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
      drule_all dse_local_agrees_mstore_memory_step >> simp[]) >>
  drule_all dse_local_agrees_mstore_other_step >> metis_tac[]
QED

Theorem dse_mstore_result_cases:
  inst.inst_opcode IN {MSTORE; MSTORE8} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> drule dse_mstore_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] SUBST1_TAC) >>
  simp[exec_write2_def, AllCaseEqs()] >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >- simp[] >>
  namedCases_on `ops` ["", "op2 ops2"] >- simp[] >>
  Cases_on `ops2` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[] >>
  Cases_on `eval_operand op2 s` >> simp[]
QED

(* NOP execution is the existing passSharedPropsTheory.mk_nop_inst_correct. *)

Theorem dse_local_agrees_key_overwrite:
  sp IN {AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ key_ok P ==>
  dse_local_agrees sp (FILTER (\(loc,(a,n)). n2w a <> k) P)
    (if sp = AddrSp_Storage then sstore k v s else tstore k v s)
    (if sp = AddrSp_Storage then sstore k v t else tstore k v t)
Proof
  strip_tac >>
  `dse_pending_space sp P s t` by fs[dse_local_agrees_def] >>
  gvs[]
  >- (drule_all dse_pending_space_sstore_overwrite >>
      disch_then (qspecl_then [`v`, `k`] assume_tac) >>
      fs[dse_local_agrees_def, dse_safety_agrees_def, dse_operational_agrees_def,
         sstore_def, lookup_var_def]) >>
  drule_all dse_pending_space_tstore_overwrite >>
  disch_then (qspecl_then [`v`, `k`] assume_tac) >>
  fs[dse_local_agrees_def, dse_safety_agrees_def, dse_operational_agrees_def,
     tstore_def, lookup_var_def]
QED

Theorem dse_local_agrees_key_insert_cover:
  sp IN {AddrSp_Storage; AddrSp_Transient} /\
  dse_local_agrees sp P s t /\ key_ok P ==>
  dse_local_agrees sp
    ((loc,(w2n k,1))::FILTER (\(loc,(a,n)). n2w a <> k) P)
    (if sp = AddrSp_Storage then sstore k v s else tstore k v s) t
Proof
  strip_tac >>
  `dse_pending_space sp P s t` by fs[dse_local_agrees_def] >>
  gvs[]
  >- (drule_all dse_pending_space_sstore_insert_cover >>
      disch_then (qspecl_then [`v`, `loc`, `k`] assume_tac) >>
      fs[dse_local_agrees_def, dse_safety_agrees_def, dse_operational_agrees_def,
         sstore_def, lookup_var_def]) >>
  drule_all dse_pending_space_tstore_insert_cover >>
  disch_then (qspecl_then [`v`, `loc`, `k`] assume_tac) >>
  fs[dse_local_agrees_def, dse_safety_agrees_def, dse_operational_agrees_def,
     tstore_def, lookup_var_def]
QED

Theorem dse_key_store_step:
  inst.inst_opcode IN {SSTORE; TSTORE} /\ ~s.vs_call_ctx.cc_static ==>
  step_inst fuel ctx inst s =
    exec_write2 (if inst.inst_opcode = SSTORE then sstore else tstore) inst s
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, SF ETA_ss]
QED

Theorem dse_key_store_ok_shape:
  inst.inst_opcode IN {SSTORE; TSTORE} /\
  step_inst fuel ctx inst s = OK s1 ==>
  ~s.vs_call_ctx.cc_static /\
  ?addr value k v.
    inst.inst_operands = [addr; value] /\
    eval_operand addr s = SOME k /\ eval_operand value s = SOME v /\
    s1 = (if inst.inst_opcode = SSTORE then sstore k v s else tstore k v s)
Proof
  strip_tac >> fs[] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
      exec_write2_def, eval_operands_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem dse_key_store_write_location:
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [addr; value] ==>
  bp_get_write_location bp inst sp =
    bp_segment_from_ops bp <|iao_ofst := addr; iao_size := SOME (Lit 1w);
                             iao_max_size := SOME (Lit 1w)|>
Proof
  strip_tac >> gvs[bp_get_write_location_def, addr_space_word_scale_def]
QED

Theorem dse_key_store_write_region:
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [addr; value] /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ eval_operand addr s = SOME k ==>
  dse_region_matches (bp_get_write_location bp inst sp) s (w2n k) 1
Proof
  strip_tac >>
  `bp_get_write_location bp inst sp =
    bp_segment_from_ops bp <|iao_ofst := addr; iao_size := SOME (Lit 1w);
                             iao_max_size := SOME (Lit 1w)|>` by
    metis_tac[dse_key_store_write_location] >>
  pop_assum SUBST1_TAC >>
  `w2n (1w:bytes32) = 1` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC) >>
  irule bp_segment_region_matches >> simp[eval_operand_def, Excl "w2n_n2w"] >>
  qexistsl_tac [`inst`, `sp`] >> gvs[bp_access_ops_def]
QED

Theorem dse_key_store_write_size:
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [addr; value] /\
  (bp_get_write_location bp inst sp).ml_size = SOME n ==> n = 1
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all dse_key_store_write_location >>
  disch_then (qspec_then `bp` assume_tac) >> fs[] >>
  drule bp_segment_size_eval >>
  simp[eval_operand_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Theorem dse_key_store_clobber_key:
  dse_pending_at cfg bp sp fn bb idx P s /\
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME k /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  MEM (loc,(a,n)) P /\ dse_inst_clobbers bp sp loc inst ==>
  (n2w a : bytes32) = k
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dse_pending_at_member >> strip_tac >>
  `?m. (bp_get_write_location bp inst sp).ml_size = SOME m` by
    (fs[dse_inst_clobbers_def, completely_contains_def] >>
     Cases_on `(bp_get_write_location bp inst sp).ml_size` >> gvs[]) >>
  drule_all dse_key_store_write_region >> strip_tac >>
  drule_all dse_key_store_write_size >> strip_tac >> gvs[] >>
  drule_all dse_pending_at_clobber_covered >> strip_tac >>
  `a = w2n k` by decide_tac >> simp[]
QED

Theorem dse_key_store_pending_step:
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME k /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s ==>
  dse_pending_at cfg bp sp fn bb (SUC idx)
    (FILTER (\(loc,(a,n)). n2w a <> k) P) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule dse_pending_at_step >>
  reverse conj_tac >- (irule dse_pending_at_filter >> simp[]) >>
  simp[MEM_FILTER] >> rpt strip_tac >>
  `n2w a = k` by metis_tac[dse_key_store_clobber_key] >> fs[]
QED

Theorem dse_key_store_pending_insert:
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst /\
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_operands = [addr; value] /\ eval_operand addr s = SOME k /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  ml_is_fixed (bp_get_write_location bp inst sp) /\
  dse_suffix_dead cfg FEMPTY bp (bp_get_write_location bp inst sp) sp fn bb (SUC idx) ==>
  dse_pending_at cfg bp sp fn bb (SUC idx)
    ((bp_get_write_location bp inst sp,(w2n k,1))::
      FILTER (\(loc,(a,n)). n2w a <> k) P) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dse_key_store_pending_step >> strip_tac >>
  drule_all dse_key_store_write_region >> strip_tac >>
  `?n. (bp_get_write_location bp inst sp).ml_size = SOME n` by
    (fs[ml_is_fixed_def] >>
     Cases_on `(bp_get_write_location bp inst sp).ml_size` >> gvs[]) >>
  drule_all dse_key_store_write_size >> strip_tac >>
  irule dse_pending_at_cons >> simp[] >>
  gvs[wordsTheory.w2n_lt]
QED

Theorem dse_local_agrees_key_store_deleted_step:
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  inst.inst_outputs = [] /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  ml_is_fixed (bp_get_write_location bp inst sp) /\
  (bp_get_write_location bp inst sp).ml_size <> SOME 0 /\
  dse_suffix_dead cfg FEMPTY bp (bp_get_write_location bp inst sp) sp fn bb
    (SUC s.vs_inst_idx) /\ step_inst fuel ctx inst s = OK s1 ==>
  ?P1. dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst.inst_opcode IN {SSTORE; TSTORE}` by fs[] >>
  `sp IN {AddrSp_Storage; AddrSp_Transient} /\
   (inst.inst_opcode = SSTORE <=> sp = AddrSp_Storage)` by gvs[] >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `key_ok P` by fs[dse_pending_at_def] >>
  drule_all dse_key_store_ok_shape >> strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexists_tac `(bp_get_write_location bp inst sp,(w2n k,1))::
    FILTER (\(loc,(a,n)). n2w a <> k) P` >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      drule_all dse_local_agrees_key_insert_cover >>
      disch_then (qspecl_then [`v`, `bp_get_write_location bp inst sp`, `k`] mp_tac) >>
      simp[]) >>
  irule dse_pending_at_allocas_extend >> qexists_tac `s` >>
  conj_tac >- (gvs[] >> simp[sstore_def, tstore_def]) >>
  irule dse_key_store_pending_insert >> metis_tac[]
QED

Theorem dse_local_agrees_other_key_write:
  wsp IN {AddrSp_Storage; AddrSp_Transient} /\ sp <> wsp /\
  dse_local_agrees sp P s t ==>
  dse_local_agrees sp P
    (if wsp = AddrSp_Storage then sstore k v s else tstore k v s)
    (if wsp = AddrSp_Storage then sstore k v t else tstore k v t)
Proof
  strip_tac >> Cases_on `sp` >>
  gvs[dse_local_agrees_def, dse_pending_space_def,
      dse_safety_agrees_def, dse_operational_agrees_def,
      dse_equiv_def, sstore_def, tstore_def, lookup_var_def,
      dse_pending_memory_def, dse_memory_byte_def]
QED

Theorem dse_key_store_other_write_location:
  inst.inst_opcode IN {SSTORE; TSTORE} /\
  sp <> (if inst.inst_opcode = SSTORE then AddrSp_Storage else AddrSp_Transient) ==>
  bp_get_write_location bp inst sp = ml_empty
Proof
  strip_tac >> Cases_on `sp` >>
  gvs[bp_get_write_location_def, is_raw_fmp_opcode_def, write_effects_def]
QED

Theorem dse_key_store_other_pending_step:
  inst.inst_opcode IN {SSTORE; TSTORE} /\
  sp <> (if inst.inst_opcode = SSTORE then AddrSp_Storage else AddrSp_Transient) /\
  dse_pending_at cfg bp sp fn bb idx P s /\
  EL idx bb.bb_instructions = inst ==>
  dse_pending_at cfg bp sp fn bb (SUC idx) P s
Proof
  strip_tac >> irule dse_pending_at_step >> simp[] >> rpt strip_tac >>
  drule_all dse_pending_at_member >> strip_tac >>
  `bp_get_write_location bp inst sp = ml_empty` by
    (irule dse_key_store_other_write_location >> fs[]) >>
  fs[dse_inst_clobbers_def, ml_empty_def, completely_contains_def]
QED

Theorem dse_local_agrees_key_store_same_step:
  ((inst.inst_opcode = SSTORE /\ sp = AddrSp_Storage) \/
   (inst.inst_opcode = TSTORE /\ sp = AddrSp_Transient)) /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  bp_ptr_sound bp s /\ bp_accesses_in_own_alloca bp inst s /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `inst.inst_opcode IN {SSTORE; TSTORE}` by fs[] >>
  `sp IN {AddrSp_Storage; AddrSp_Transient} /\
   (inst.inst_opcode = SSTORE <=> sp = AddrSp_Storage)` by gvs[] >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  `key_ok P` by fs[dse_pending_at_def] >>
  drule_all dse_key_store_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand addr t = SOME k /\ eval_operand value t = SOME v` by metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  `~t.vs_call_ctx.cc_static` by
    gvs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  qexistsl_tac [`FILTER (\(loc,(a,n)). n2w a <> k) P`,
    `if sp = AddrSp_Storage then sstore k v t else tstore k v t`] >>
  conj_tac
  >- (drule_all dse_key_store_step >>
      disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
      simp[exec_write2_def] >> Cases_on `sp = AddrSp_Storage` >> fs[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      drule_all dse_local_agrees_key_overwrite >>
      disch_then (qspecl_then [`v`, `k`] mp_tac) >> simp[]) >>
  irule dse_pending_at_allocas_extend >> qexists_tac `s` >>
  conj_tac >- (gvs[] >> simp[sstore_def, tstore_def]) >>
  irule dse_key_store_pending_step >> metis_tac[]
QED

Theorem dse_local_agrees_key_store_other_step:
  inst.inst_opcode IN {SSTORE; TSTORE} /\
  sp <> (if inst.inst_opcode = SSTORE then AddrSp_Storage else AddrSp_Transient) /\
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
  drule_all dse_key_store_ok_shape >> strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand addr t = SOME k /\ eval_operand value t = SOME v` by metis_tac[] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  `~t.vs_call_ctx.cc_static` by
    gvs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  qexists_tac `if inst.inst_opcode = SSTORE then sstore k v t else tstore k v t` >>
  conj_tac
  >- (drule_all dse_key_store_step >>
      disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
      simp[exec_write2_def] >> Cases_on `inst.inst_opcode = SSTORE` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      Cases_on `inst.inst_opcode = SSTORE` >> simp[]
      >- (irule (SRULE [] (Q.INST [`wsp` |-> `AddrSp_Storage`]
            dse_local_agrees_other_key_write)) >> fs[]) >>
      irule (SRULE [] (Q.INST [`wsp` |-> `AddrSp_Transient`]
        dse_local_agrees_other_key_write)) >> fs[]) >>
  irule dse_pending_at_allocas_extend >> qexists_tac `s` >>
  conj_tac >- (gvs[] >> simp[sstore_def, tstore_def]) >>
  irule dse_key_store_other_pending_step >> gvs[]
QED

Theorem dse_local_agrees_key_store_step:
  inst.inst_opcode IN {SSTORE; TSTORE} /\
  dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  alloca_inv s /\ bp_ptr_sound bp s /\
  bp_accesses_in_own_alloca bp inst s /\ step_inst fuel ctx inst s = OK s1 ==>
  ?P1 t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P1 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P1 s1
Proof
  strip_tac >>
  Cases_on `sp = (if inst.inst_opcode = SSTORE then AddrSp_Storage else AddrSp_Transient)`
  >- (irule dse_local_agrees_key_store_same_step >> gvs[] >> metis_tac[]) >>
  drule_all dse_local_agrees_key_store_other_step >> metis_tac[]
QED

Theorem dse_key_store_result_cases:
  inst.inst_opcode IN {SSTORE; TSTORE} /\ ~s.vs_call_ctx.cc_static ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  strip_tac >> drule_all dse_key_store_step >>
  disch_then (qspecl_then [`fuel`, `ctx`] SUBST1_TAC) >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >- simp[exec_write2_def] >>
  namedCases_on `ops` ["", "op2 ops2"] >- simp[exec_write2_def] >>
  Cases_on `ops2` >> simp[exec_write2_def] >>
  Cases_on `eval_operand op s` >> simp[] >>
  Cases_on `eval_operand op2 s` >> simp[]
QED
