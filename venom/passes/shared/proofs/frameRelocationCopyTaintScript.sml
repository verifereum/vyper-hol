Theory frameRelocationCopyTaint
Ancestors frameRelocationCopySteps frameRelocationMemory ptrDiscipline
  codegenRel venomState venomExecSemantics finite_map pred_set words

Definition demand_taint_def:
  demand_taint R (M:num set) (N:num set) <=>
    !a b. R a b /\ b IN N ==> a IN M
End

Theorem step_taint_mcopy_mem:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  s' = mcopy (w2n dst) (w2n src) (w2n sz) s ==>
  (a IN (step_taint inst s s' tn).t_mem <=>
   if w2n dst <= a /\ a < w2n dst + w2n sz
   then w2n src + (a - w2n dst) IN tn.t_mem else a IN tn.t_mem)
Proof
  strip_tac >>
  `new_site_bytes s s' = {}` by
    (irule new_site_bytes_unchanged >>
     simp[mcopy_def, write_memory_with_expansion_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, sized_source_write_range_def,
       range_bytes_def, written_taint_def] >>
  IF_CASES_TAC >> simp[] >> eq_tac >> rpt strip_tac >> gvs[]
  >- (qexists_tac `a - w2n dst` >> simp[] >> decide_tac) >>
  decide_tac
QED

Theorem demand_taint_mcopy:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME dstT /\ eval_operand ops t = SOME srcT /\
  eval_operand opn t = SOME sz /\
  s' = mcopy (w2n dst) (w2n src) (w2n sz) s /\
  t' = mcopy (w2n dstT) (w2n srcT) (w2n sz) t /\
  demand_taint R tn.t_mem un.t_mem /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst+w2n sz ==>
    w2n dstT <= b /\ b < w2n dstT+w2n sz /\
    R (w2n src+(a-w2n dst)) (w2n srcT+(b-w2n dstT))) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT+w2n sz)) ==>
  demand_taint next (step_taint inst s s' tn).t_mem
    (step_taint inst t t' un).t_mem
Proof
  strip_tac >> simp[demand_taint_def] >> rpt gen_tac >> strip_tac >>
  `!i. i IN (step_taint inst s s' tn).t_mem <=>
    if w2n dst <= i /\ i < w2n dst+w2n sz
    then w2n src+(i-w2n dst) IN tn.t_mem else i IN tn.t_mem` by
    (rpt gen_tac >> irule step_taint_mcopy_mem >> metis_tac[]) >>
  `!i. i IN (step_taint inst t t' un).t_mem <=>
    if w2n dstT <= i /\ i < w2n dstT+w2n sz
    then w2n srcT+(i-w2n dstT) IN un.t_mem else i IN un.t_mem` by
    (rpt gen_tac >> irule step_taint_mcopy_mem >> metis_tac[]) >>
  qpat_x_assum `!a b. next a b /\ _ /\ _ ==> _`
    (qspecl_then [`a`, `b`] mp_tac) >>
  qpat_x_assum `!a b. next a b /\ ~_ ==> _`
    (qspecl_then [`a`, `b`] mp_tac) >>
  Cases_on `w2n dst <= a /\ a < w2n dst+w2n sz` >>
  simp[] >> rpt strip_tac >> gvs[demand_taint_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[]
QED
