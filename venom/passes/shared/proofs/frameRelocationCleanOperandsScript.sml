Theory frameRelocationCleanOperands
Ancestors frameRelocationGuardedValues frameRelocationOpaque
  frameRelocationReachableSupport frameRelocationArithmeticClassification
  concretizePtrParamSupport ptrDiscipline finite_map list

Theorem taint_ok_operand_exclusion:
  taint_ok fn tn inst s /\ MEM op inst.inst_operands /\
  ~MEM inst.inst_opcode [ASSIGN; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] ==>
  op_taint tn op = {}
Proof
  simp[taint_ok_def] >> metis_tac[]
QED

Theorem disciplined_clean_scalar:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
  MEM (Var v) inst.inst_operands /\ FLOOKUP rv v = NONE ==>
  clean_scalar (retpc_var fn) rv tn v
Proof
  strip_tac >> simp[clean_scalar_def] >> conj_tac
  >- (strip_tac >> drule_all disciplined_retpc_operand_use >> gvs[]) >>
  irule taint_ok_operand_exclusion >> metis_tac[listTheory.MEM]
QED

Theorem disciplined_scalar_operand:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  ~MEM inst.inst_opcode [ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
  MEM op inst.inst_operands /\
  (!v. op = Var v ==> FLOOKUP rv v = NONE) /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >> irule guarded_scalar_operand >>
  simp[] >> goal_assum (drule_at Any) >>
  rpt strip_tac >> irule disciplined_clean_scalar >> metis_tac[]
QED

Theorem reachable_sub_scalar_agreement[local]:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  resolved_frame_ok birth cache PG G om rp rv ids frames /\
  o1_fn_shape ctx fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_opcode = SUB /\
  inst.inst_operands = [a; Var w] /\ s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R Obs s t ==>
  eval_operand (Var w) s = eval_operand (Var w) t
Proof
  strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok P fn` by metis_tac[EVERY_MEM] >>
  `FLOOKUP rv w = NONE` by
    (irule resolved_sub_right_absent >>
     qexistsl_tac [`P`, `a`, `fn`, `inst`] >> simp[] >>
     rpt strip_tac >> drule_all reachable_resolved_support >> simp[]) >>
  `~MEM inst.inst_opcode [ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]` by simp[] >>
  `MEM (Var w) inst.inst_operands` by simp[] >>
  `!v. Var w = Var v ==> FLOOKUP rv v = NONE` by simp[] >>
  drule_all disciplined_scalar_operand >> simp[]
QED
