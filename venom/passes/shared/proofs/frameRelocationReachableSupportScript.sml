Theory frameRelocationReachableSupport
Ancestors concretizePtrParamSupport frameResolvedTrace
  frameRelocationArithmeticClassification ptrDiscipline pointerConfinedDefs
  venomInst venomWf finite_map

Theorem resolved_static_support:
  ptr_static_support P fn G /\
  (!v e. FLOOKUP rv v = SOME e ==> FLOOKUP G v = SOME (SND e)) ==>
  !u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn
Proof
  simp[ptr_static_support_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP rv u` >> gvs[] >>
  metis_tac[]
QED

Theorem reachable_resolved_support:
  frame_reachable vs0 ctx stk PG G tn fn inst s /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions /\
  resolved_frame_ok dyn birth cache PG G om rp rv ids frames ==>
  !u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn
Proof
  rpt strip_tac >>
  drule_all ptr_frame_current_static >> strip_tac >>
  drule resolved_frame_erasure >> strip_tac >>
  drule_all resolved_static_support >> simp[]
QED
