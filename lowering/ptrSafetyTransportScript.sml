Theory ptrSafetyTransport
Ancestors ptrSafeRun ptrDiscipline arithmetic

Theorem ptr_inst_ok_lower_bound_transport:
  lo0 <= lo /\ allocas_from lo s /\
  ptr_inst_ok D lo0 fuel ctx fn G tn inst s ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  pure_rewrite_tac [ptr_inst_ok_def] >> strip_tac >>
  `access_ok lo G fn inst s` by
    (qpat_x_assum `access_ok lo0 _ _ _ _` mp_tac >>
     qpat_x_assum `lo0 <= lo` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[access_ok_def] >> rpt strip_tac >>
     gvs[] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
  asm_rewrite_tac[]
QED
