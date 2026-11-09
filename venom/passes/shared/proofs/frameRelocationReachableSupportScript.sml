Theory frameRelocationReachableSupport
Ancestors concretizePtrParamSupport frameResolvedTrace
  frameRelocationArithmeticClassification ptrDiscipline pointerConfinedDefs
  venomInst venomWf finite_map

Theorem resolved_static_support:
  ptr_static_support P fn G /\ SND o_f rv = G ==>
  !u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn
Proof
  simp[ptr_static_support_def, FLOOKUP_o_f] >>
  rpt strip_tac >> Cases_on `FLOOKUP rv u` >> gvs[] >>
  first_x_assum (qspec_then `u` mp_tac) >> simp[FLOOKUP_o_f]
QED

Theorem reachable_resolved_support:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  resolved_frame_ok birth cache PG G om rp rv ids frames ==>
  !u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn
Proof
  rpt strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  drule resolved_frame_erasure >> strip_tac >>
  drule_all resolved_static_support >> simp[]
QED

Theorem reachable_sub_support_probe[local]:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  resolved_frame_ok birth cache PG G om rp rv ids frames /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = SUB /\
  inst.inst_operands = [a;Var w] ==>
  FLOOKUP rv w = NONE
Proof
  strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok P fn` by metis_tac[listTheory.EVERY_MEM] >>
  irule resolved_sub_right_absent >>
  qexistsl_tac [`P`, `a`, `fn`, `inst`] >> simp[] >>
  rpt strip_tac >> drule_all reachable_resolved_support >> simp[]
QED
