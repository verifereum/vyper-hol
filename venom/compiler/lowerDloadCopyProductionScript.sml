Theory lowerDloadCopyProduction
Ancestors
  lowerDloadMemoryExecution lowerDloadSnapshot lowerDloadEffectTransport
  lowerDloadSharedState lowerDloadRelocation venomExecSemantics venomState
  ptrDiscipline words pred_set

Theorem ld_mcopy_memory_backward:
  i.inst_opcode = MCOPY /\ i.inst_operands = [dst;src;sz] /\
  eval_operand dst s = SOME p /\ eval_operand src s = SOME r /\
  eval_operand sz s = SOME n /\
  eval_operand dst t = SOME q /\ eval_operand src t = SOME u /\
  eval_operand sz t = SOME n /\ step_inst fuelT CT i t = OK t' /\
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> ((w2n p <= a /\ a < w2n p+w2n n) <=>
                       (w2n q <= b /\ b < w2n q+w2n n))) /\
  (!a b. R a b /\ w2n p <= a /\ a < w2n p+w2n n ==>
     a-w2n p = b-w2n q) /\
  (!k. k<w2n n ==> R (w2n r+k) (w2n u+k)) ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_byte_rel R
      ((Ts DIFF {a | w2n p<=a /\ a<w2n p+w2n n}) UNION
        {w2n p+k | k<w2n n /\ w2n r+k IN Ts})
      ((Tt DIFF {b | w2n q<=b /\ b<w2n q+w2n n}) UNION
        {w2n q+k | k<w2n n /\ w2n u+k IN Tt})
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t
Proof
  strip_tac >>
  `step_inst fuelS CS i s = OK (mcopy (w2n p) (w2n r) (w2n n) s) /\
   t' = mcopy (w2n q) (w2n u) (w2n n) t` by
    (irule ld_mcopy_execution_backward >> simp[] >> metis_tac[]) >>
  gvs[] >>
  simp[ld_mcopy_memory_restore] >>
  irule (SRULE [arithmeticTheory.ADD_COMM] ld_byte_rel_mcopy) >> simp[]
QED

Theorem ld_mcopy_shared_state_transport:
  i.inst_opcode = MCOPY /\ i.inst_outputs = [] /\
  ld_shared_state tn un s t ==>
  ld_shared_state
    (step_taint i s (mcopy p r n s) tn)
    (step_taint i t (mcopy q u n t) un)
    (mcopy p r n s) (mcopy q u n t)
Proof
  strip_tac >> irule ld_shared_state_memory_transport >>
  qexistsl_tac [`s`,`t`,`tn`,`un`] >>
  simp[ld_mcopy_memory_restore, step_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def]
QED
