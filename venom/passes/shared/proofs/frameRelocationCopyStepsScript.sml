Theory frameRelocationCopySteps
Ancestors frameRelocationMemory frameRelocationDemand frameRelocationLocal
  frameRelocationValues venomExecSemantics venomState venomInst words

Theorem demand_agree_mcopy:
  demand_agree R (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory) /\
  (!a b. next a b /\ d <= a /\ a < d+n ==>
    e <= b /\ b < e+n /\ R (p+(a-d)) (q+(b-e))) /\
  (!a b. next a b /\ ~(d <= a /\ a < d+n) ==>
    R a b /\ ~(e <= b /\ b < e+n)) ==>
  demand_agree next (\a. read_byte a (mcopy d p n s).vs_memory)
    (\b. read_byte b (mcopy e q n t).vs_memory)
Proof
  strip_tac >> irule demand_agree_producer_update >>
  qexistsl_tac [`R`, `\a. read_byte (p+(a-d)) s.vs_memory`,
    `\b. read_byte (q+(b-e)) t.vs_memory`,
    `\a. read_byte a s.vs_memory`, `\b. read_byte b t.vs_memory`,
    `\a. d <= a /\ a < d+n`, `\b. e <= b /\ b < e+n`] >>
  simp[read_byte_mcopy] >> gvs[demand_agree_def] >> metis_tac[]
QED

Theorem local_rel_memory_frame:
  local_rel P ptr B R Obs s t /\
  s'.vs_vars = s.vs_vars /\ t'.vs_vars = t.vs_vars /\
  demand_agree next (\a. read_byte a s'.vs_memory)
    (\b. read_byte b t'.vs_memory) /\ Obs s' t' ==>
  local_rel P ptr B next Obs s' t'
Proof
  simp[local_rel_def, variable_domains_def, variables_agree_on_def,
       local_values_def, lookup_var_def] >> metis_tac[]
QED

Theorem local_rel_mcopy:
  local_rel P ptr B R Obs s t /\
  (!a b. next a b /\ d <= a /\ a < d+n ==>
    e <= b /\ b < e+n /\ R (p+(a-d)) (q+(b-e))) /\
  (!a b. next a b /\ ~(d <= a /\ a < d+n) ==>
    R a b /\ ~(e <= b /\ b < e+n)) /\
  Obs (mcopy d p n s) (mcopy e q n t) ==>
  local_rel P ptr B next Obs (mcopy d p n s) (mcopy e q n t)
Proof
  strip_tac >> irule local_rel_memory_frame >>
  conj_tac >- simp[] >> conj_tac
  >- (irule demand_agree_mcopy >> metis_tac[local_rel_demand]) >>
  qexistsl_tac [`R`, `s`, `t`] >> simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem local_rel_mcopy_step:
  inst.inst_opcode = MCOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
  eval_operand opn s = SOME sz /\
  eval_operand opd t = SOME dstT /\ eval_operand ops t = SOME srcT /\
  eval_operand opn t = SOME sz /\ local_rel P ptr B R Obs s t /\
  (!a b. next a b /\ w2n dst <= a /\ a < w2n dst+w2n sz ==>
    w2n dstT <= b /\ b < w2n dstT+w2n sz /\
    R (w2n src+(a-w2n dst)) (w2n srcT+(b-w2n dstT))) /\
  (!a b. next a b /\ ~(w2n dst <= a /\ a < w2n dst+w2n sz) ==>
    R a b /\ ~(w2n dstT <= b /\ b < w2n dstT+w2n sz)) /\
  Obs (mcopy (w2n dst) (w2n src) (w2n sz) s)
      (mcopy (w2n dstT) (w2n srcT) (w2n sz) t) ==>
  ?s' t'. step_inst_base inst s = OK s' /\ step_inst_base inst t = OK t' /\
    local_rel P ptr B next Obs s' t'
Proof
  strip_tac >>
  qexistsl_tac [`mcopy (w2n dst) (w2n src) (w2n sz) s`,
               `mcopy (w2n dstT) (w2n srcT) (w2n sz) t`] >>
  simp[step_inst_base_def] >> irule local_rel_mcopy >> metis_tac[]
QED
