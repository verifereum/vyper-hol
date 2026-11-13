Theory deadStoreElimExternalCopySteps
Ancestors
  deadStoreElimCopySteps deadStoreElimStoreSteps
  deadStoreElimLocal deadStoreElimPending deadStoreElimLocations
  deadStoreElimLiveness deadStoreElimSafety deadStoreElimDefs
  deadStoreElimEquiv venomExecSemantics venomState venomMemDefs
  venomMemProps venomEffects venomInst basePtrDefs memLocDefs list
  deadStoreElimFrame
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_external_copy_step:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} ==>
  step_inst fuel ctx inst s =
    case inst.inst_operands of
      [op_dst; src; szop] =>
        (case (eval_operand op_dst s, eval_operand src s, eval_operand szop s) of
           (SOME a, SOME b, SOME n) =>
             OK (write_memory_with_expansion (w2n a)
               (TAKE (w2n n) (DROP (w2n b)
                 (if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
                  else if inst.inst_opcode = CODECOPY then s.vs_code
                  else s.vs_data_section) ++ REPLICATE (w2n n) 0w)) s)
         | _ => Error "undefined operand")
    | _ => Error (if inst.inst_opcode = CALLDATACOPY then "calldatacopy requires 3 operands"
                  else if inst.inst_opcode = CODECOPY then "codecopy requires 3 operands"
                  else "dloadbytes requires 3 operands")
Proof
  simp[] >> strip_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs]
QED

Theorem dse_external_copy_ok_shape:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?op_dst src szop a b n bytes.
    inst.inst_operands = [op_dst; src; szop] /\
    eval_operand op_dst s = SOME a /\ eval_operand src s = SOME b /\
    eval_operand szop s = SOME n /\
    bytes = TAKE (w2n n) (DROP (w2n b)
      (if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
       else if inst.inst_opcode = CODECOPY then s.vs_code else s.vs_data_section) ++
      REPLICATE (w2n n) 0w) /\
    LENGTH bytes = w2n n /\ s1 = write_memory_with_expansion (w2n a) bytes s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule dse_external_copy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> gvs[AllCaseEqs(), LENGTH_TAKE_EQ] >> metis_tac[]
QED

Theorem dse_external_copy_match:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} /\
  dse_local_agrees sp P s t /\
  inst.inst_operands = [op_dst; src; szop] /\
  eval_operand op_dst s = SOME a /\ eval_operand src s = SOME b /\
  eval_operand szop s = SOME n /\
  bytes = TAKE (w2n n) (DROP (w2n b)
    (if inst.inst_opcode = CALLDATACOPY then s.vs_call_ctx.cc_calldata
     else if inst.inst_opcode = CODECOPY then s.vs_code else s.vs_data_section) ++
    REPLICATE (w2n n) 0w) ==>
  step_inst fuel ctx inst t = OK (write_memory_with_expansion (w2n a) bytes t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand op_dst t = SOME a /\ eval_operand src t = SOME b /\
   eval_operand szop t = SOME n` by metis_tac[] >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_code = t.vs_code /\
   s.vs_data_section = t.vs_data_section` by
    (fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def]) >>
  drule dse_external_copy_step >>
  disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >> simp[]
QED

Theorem dse_local_agrees_external_copy_memory_step:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_external_copy_ok_shape >> strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexistsl_tac [
    `FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P`,
    `write_memory_with_expansion (w2n a) bytes t`] >>
  conj_tac >- (irule dse_external_copy_match >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_memory_overwrite >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_copy_pending_memory_step >> fs[] >> metis_tac[]
QED

Theorem dse_local_agrees_external_copy_deleted_step:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_external_copy_ok_shape >> strip_tac >>
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
  irule dse_copy_pending_insert_step >> fs[] >> metis_tac[]
QED

Theorem dse_local_agrees_external_copy_other_step:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} /\
  sp <> AddrSp_Memory /\ dse_local_agrees sp P s t /\
  dse_pending_at cfg bp sp fn bb s.vs_inst_idx P s /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK s1 ==>
  ?t1. step_inst fuel ctx inst t = OK t1 /\
    dse_local_agrees sp P (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    dse_pending_at cfg bp sp fn bb (SUC s.vs_inst_idx) P s1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_external_copy_ok_shape >> strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexists_tac `write_memory_with_expansion (w2n a) bytes t` >>
  conj_tac >- (irule dse_external_copy_match >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_other_memory_write >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_copy_other_pending_step >> fs[] >> metis_tac[]
QED

Theorem dse_local_agrees_external_copy_step:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `sp = AddrSp_Memory`
  >- (qpat_x_assum `sp = AddrSp_Memory` SUBST_ALL_TAC >>
      drule_all dse_local_agrees_external_copy_memory_step >> simp[]) >>
  drule_all dse_local_agrees_external_copy_other_step >> metis_tac[]
QED

Theorem dse_external_copy_result_cases:
  inst.inst_opcode IN {CALLDATACOPY; CODECOPY; DLOADBYTES} ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e)
Proof
  disch_tac >> drule dse_external_copy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] SUBST1_TAC) >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >- simp[] >>
  namedCases_on `ops` ["", "op2 ops2"] >- simp[] >>
  namedCases_on `ops2` ["", "op3 ops3"] >- simp[] >>
  Cases_on `ops3` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[] >>
  Cases_on `eval_operand op2 s` >> simp[] >>
  Cases_on `eval_operand op3 s` >> simp[]
QED
