Theory lowerDloadByteStoreProduction
Ancestors
  lowerDloadMemoryExecution lowerDloadRelocation lowerDloadEffectTransport
  lowerDloadSharedState venomExecSemantics venomState ptrDiscipline
  regularCallEmitSim regularMemorySim codegenRel words list pred_set

Theorem ld_mstore8_read_byte:
  read_memory a 1 (mstore8 p v s) =
    if a = p then [w2w v : word8] else read_memory a 1 s
Proof
  `mstore8 p v s = write_memory_with_expansion p [w2w v] s` by
    simp[mstore8_def, write_memory_with_expansion_def] >>
  simp[read_memory_def, venom_returndata_read_byte,
       GENLIST, read_byte_write_memory_with_expansion] >>
  Cases_on `a = p` >> simp[] >>
  `~(p <= a /\ a < p+1)` by decide_tac >> simp[]
QED

Theorem ld_mstore8_memory_backward:
  i.inst_opcode = MSTORE8 /\ i.inst_operands = [dst;value] /\
  eval_operand dst s = SOME p /\ eval_operand value s = SOME v /\
  eval_operand dst t = SOME q /\ eval_operand value t = SOME w /\
  step_inst fuelT CT i t = OK t' /\
  ld_byte_rel R Ts Tt (\a. read_memory a 1 s) (\b. read_memory b 1 t) /\
  (!a b. R a b ==> (a = w2n p <=> b = w2n q)) /\
  (w2n q IN Ut ==> w2n p IN Us) /\
  (w2n p NOTIN Us ==> (w2w v : word8) = w2w w) ==>
  ?s'. step_inst fuelS CS i s = OK s' /\
    ld_byte_rel R ((Ts DIFF {w2n p}) UNION (Us INTER {w2n p}))
                  ((Tt DIFF {w2n q}) UNION (Ut INTER {w2n q}))
      (\a. read_memory a 1 s') (\b. read_memory b 1 t') /\
    (s' with vs_memory := s.vs_memory) = s /\
    (t' with vs_memory := t.vs_memory) = t
Proof
  strip_tac >>
  `step_inst fuelS CS i s = OK (mstore8 (w2n p) v s) /\
   t' = mstore8 (w2n q) w t` by
    (irule ld_mstore8_execution_backward >> simp[] >> metis_tac[]) >>
  gvs[] >> simp[ld_mstore8_memory_restore, ld_mstore8_read_byte] >>
  fs[ld_byte_rel_def] >> rpt gen_tac >> disch_tac >>
  Cases_on `a = w2n p`
  >- (`b = w2n q` by metis_tac[] >> gvs[])
  >> `b <> w2n q` by metis_tac[] >> simp[] >> metis_tac[]
QED

Theorem ld_mstore8_shared_state_transport:
  i.inst_opcode = MSTORE8 /\ i.inst_outputs = [] /\
  ld_shared_state tn un s t ==>
  ld_shared_state
    (step_taint i s (mstore8 p v s) tn)
    (step_taint i t (mstore8 q w t) un)
    (mstore8 p v s) (mstore8 q w t)
Proof
  strip_tac >> irule ld_shared_state_memory_transport >>
  qexistsl_tac [`s`,`t`,`tn`,`un`] >>
  simp[ld_mstore8_memory_restore, step_taint_def, store_taint_def,
       imm_taint_def, adopt_reset_def]
QED
