Theory deadStoreElimReturnDataCopySteps
Ancestors
  deadStoreElimExternalCopySteps deadStoreElimCopySteps deadStoreElimStoreSteps
  deadStoreElimLocal deadStoreElimPending deadStoreElimLocations
  deadStoreElimLiveness deadStoreElimSafety deadStoreElimDefs
  deadStoreElimEquiv deadStoreElimTerminalEquiv stateEquiv venomExecSemantics venomState venomMemDefs
  venomMemProps venomEffects venomInst basePtrDefs memLocDefs list
Libs
  deadStoreElimFrameLib

val _ = augment_srw_ss [deadStoreElimFrameLib.frame_ss];

Theorem dse_returndatacopy_not_effects_in_space:
  inst.inst_opcode = RETURNDATACOPY ==> ~effects_in_space sp inst
Proof
  strip_tac >> Cases_on `sp` >>
  simp[effects_in_space_def, write_effects_def, read_effects_def,
       pred_setTheory.SUBSET_DEF] >>
  disch_then (SUBST1_TAC o SYM) >> simp[]
QED

Theorem dse_returndatacopy_step:
  inst.inst_opcode = RETURNDATACOPY ==>
  step_inst fuel ctx inst s =
    case inst.inst_operands of
      [op_dst; src; szop] =>
        (case (eval_operand op_dst s, eval_operand src s, eval_operand szop s) of
           (SOME a, SOME b, SOME n) =>
             if LENGTH s.vs_returndata < w2n b + w2n n then
               Abort ExHalt_abort (halt_state (set_returndata [] s))
             else OK (write_memory_with_expansion (w2n a)
                 (TAKE (w2n n) (DROP (w2n b) s.vs_returndata)) s)
         | _ => Error "undefined operand")
    | _ => Error "returndatacopy requires 3 operands"
Proof
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, arithmeticTheory.GREATER_DEF]
QED

Theorem dse_returndatacopy_ok_shape:
  inst.inst_opcode = RETURNDATACOPY /\ step_inst fuel ctx inst s = OK s1 ==>
  ?op_dst src szop a b n bytes.
    inst.inst_operands = [op_dst; src; szop] /\
    eval_operand op_dst s = SOME a /\ eval_operand src s = SOME b /\
    eval_operand szop s = SOME n /\
    w2n b + w2n n <= LENGTH s.vs_returndata /\
    bytes = TAKE (w2n n) (DROP (w2n b) s.vs_returndata) /\
    LENGTH bytes = w2n n /\ s1 = write_memory_with_expansion (w2n a) bytes s
Proof
  strip_tac >> drule dse_returndatacopy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `w2n n <= LENGTH s.vs_returndata - w2n b` by decide_tac >>
  simp[LENGTH_TAKE_EQ] >> metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem dse_returndatacopy_match:
  inst.inst_opcode = RETURNDATACOPY /\ dse_local_agrees sp P s t /\
  inst.inst_operands = [op_dst; src; szop] /\
  eval_operand op_dst s = SOME a /\ eval_operand src s = SOME b /\
  eval_operand szop s = SOME n /\ w2n b + w2n n <= LENGTH s.vs_returndata /\
  bytes = TAKE (w2n n) (DROP (w2n b) s.vs_returndata) ==>
  step_inst fuel ctx inst t = OK (write_memory_with_expansion (w2n a) bytes t)
Proof
  strip_tac >>
  `!op. eval_operand op s = eval_operand op t` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `eval_operand op_dst t = SOME a /\ eval_operand src t = SOME b /\
   eval_operand szop t = SOME n` by metis_tac[] >>
  `s.vs_returndata = t.vs_returndata` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  drule dse_returndatacopy_step >>
  disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >> gvs[]
QED

Theorem dse_local_agrees_returndatacopy_step:
  inst.inst_opcode = RETURNDATACOPY /\ dse_local_agrees sp P s t /\
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
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def, AllCaseEqs()] >>
  drule_all dse_returndatacopy_ok_shape >> strip_tac >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    fs[dse_local_agrees_def, dse_operational_agrees_def] >>
  qexistsl_tac [
    `if sp = AddrSp_Memory then
       FILTER (\(loc,(b,m)). ~(w2n a <= b /\ b+m <= w2n a+LENGTH bytes)) P
     else P`, `write_memory_with_expansion (w2n a) bytes t`] >>
  conj_tac >- (irule dse_returndatacopy_match >> metis_tac[]) >>
  Cases_on `sp = AddrSp_Memory`
  >- (qpat_x_assum `sp = AddrSp_Memory` SUBST_ALL_TAC >>
      pure_rewrite_tac[REFL_CLAUSE, COND_CLAUSES] >>
      conj_tac
      >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
          qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
          irule dse_local_agrees_inst_idx >>
          irule dse_local_agrees_memory_overwrite >> simp[]) >>
      qpat_x_assum `s1 = _` SUBST1_TAC >>
      irule dse_copy_pending_memory_step >> simp[] >> metis_tac[]) >>
  qpat_assum `sp <> AddrSp_Memory` (fn th => rewrite_tac[th]) >> conj_tac
  >- (qpat_x_assum `s1 = _` SUBST1_TAC >>
      qpat_x_assum `s.vs_inst_idx = t.vs_inst_idx` (fn th => rewrite_tac[th]) >>
      irule dse_local_agrees_inst_idx >>
      irule dse_local_agrees_other_memory_write >> simp[]) >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  irule dse_copy_other_pending_step >> simp[] >> metis_tac[]
QED

Theorem dse_returndatacopy_result_cases:
  inst.inst_opcode = RETURNDATACOPY ==>
  (?s1. step_inst fuel ctx inst s = OK s1) \/
  (?e. step_inst fuel ctx inst s = Error e) \/
  step_inst fuel ctx inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  disch_tac >> drule dse_returndatacopy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] SUBST1_TAC) >>
  namedCases_on `inst.inst_operands` ["", "op ops"] >- simp[] >>
  namedCases_on `ops` ["", "op2 ops2"] >- simp[] >>
  namedCases_on `ops2` ["", "op3 ops3"] >- simp[] >>
  Cases_on `ops3` >> simp[] >>
  Cases_on `eval_operand op s` >> simp[] >>
  Cases_on `eval_operand op2 s` >> simp[] >>
  Cases_on `eval_operand op3 s` >> simp[] >> IF_CASES_TAC >> simp[]
QED

Theorem dse_returndatacopy_abort_match:
  inst.inst_opcode = RETURNDATACOPY /\ dse_local_agrees sp P s t /\
  step_inst fuel ctx inst s = Abort abort_kind s1 ==>
  step_inst fuel ctx inst t = Abort ExHalt_abort (halt_state (set_returndata [] t))
Proof
  strip_tac >>
  `!op. eval_operand op t = eval_operand op s` by
    (fs[dse_local_agrees_def] >> metis_tac[dse_safety_agrees_eval_operand]) >>
  `t.vs_returndata = s.vs_returndata` by
    fs[dse_local_agrees_def, dse_pending_space_def, dse_equiv_def] >>
  drule dse_returndatacopy_step >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  simp[] >> gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule dse_returndatacopy_step >>
  disch_then (qspecl_then [`t`, `fuel`, `ctx`] mp_tac) >> simp[]
QED

Theorem dse_returndatacopy_non_ok:
  inst.inst_opcode = RETURNDATACOPY /\ dse_local_agrees sp P s t /\
  ~(?s1. step_inst fuel ctx inst s = OK s1) ==>
  (?e. step_inst fuel ctx inst s = Error e) \/
  lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp)
    (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  strip_tac >> drule dse_returndatacopy_result_cases >>
  disch_then (qspecl_then [`s`, `fuel`, `ctx`] mp_tac) >>
  strip_tac >- metis_tac[] >- metis_tac[] >>
  drule_all dse_returndatacopy_abort_match >>
  simp[] >> strip_tac >> simp[lift_result_def] >>
  irule dse_equiv_halt_state >> irule dse_equiv_set_returndata >>
  irule dse_pending_space_equiv >> fs[dse_local_agrees_def] >> metis_tac[]
QED
