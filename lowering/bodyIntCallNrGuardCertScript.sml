Theory bodyIntCallNrGuardCert
Ancestors
  gasExemptCert gasSummary fragGasMode fragGasPath fragGasPathMem
  vyperState venomState

(* The empty Boolean-read prefix is an actual marked execution. *)
Theorem gas_exempt_cert_guarded:
  (!st gs. b (st with gas_obs := gs) = b st) /\
  b es /\ ~s.vs_halted /\
  (!st. b st ==> target st = source st) /\
  gas_exempt_cert memory tops (ctx,func) source
    (es with gas_obs := [],s) marks (err,ee) endpoint ==>
  gas_exempt_cert memory tops (ctx,func) target
    (es,s) marks (err,ee) endpoint
Proof
  strip_tac >>
  `target = bind (\st. (INL (b st),st))
                  (\yes. if yes then source else target)` by
    (simp[FUN_EQ_THM, bind_def] >> qx_gen_tac `st` >>
     Cases_on `b st` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  PairCases_on `endpoint` >>
  `marks = [] ++ marks` by simp[] >>
  pop_assum (fn th => GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o RAND_CONV) empty_rewrites [th]) >>
  irule gas_exempt_cert_bind_bool >>
  qexistsl_tac [`es`,`s`,`T`] >>
  simp[gas_marked_exec_def, gas_marked_path_def] >>
  Cases_on `memory` >> simp[] >>
  metis_tac[gas_path_rules, gas_path_mem_rules]
QED
