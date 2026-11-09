Theory dftGasInvMemoryRanges
Ancestors
  dftGasInvTerminalReach dftGasInvMemoryObservation o1ContractCfgNorm
  unitMemInv contextCodegenRel codegenRel venomState venomInst list

Theorem inv_non_dret_ranges_cong:
  inst.inst_opcode <> DRET /\
  (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op t) ==>
  inst_mem_ranges inst s = inst_mem_ranges inst t
Proof
  strip_tac >>
  `source_memory_read_ranges inst s = source_memory_read_ranges inst t` by
    (irule supply_read_ranges_cong >> simp[]) >>
  simp[inst_mem_ranges_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[source_memory_write_ranges_def] >>
  simp[fixed_source_write_range_def, sized_source_write_range_def] >>
  namedCases_on `inst.inst_operands` ["", "o1 os1"] >> gvs[] >>
  namedCases_on `os1` ["", "o2 os2"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os2` ["", "o3 os3"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os3` ["", "o4 os4"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os4` ["", "o5 os5"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os5` ["", "o6 os6"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  namedCases_on `os6` ["", "o7 os7"] >> gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  Cases_on `os7` >> gvs[DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem inv_reachable_memory_ranges:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C initial.vs_labels /\ o1_run_state_ok initial /\
  ev_reachable orc initial C' p d fn' inst t /\
  inv_memory_observation inst.inst_opcode ==>
  ?fn sS bb bb'. MEM fn C.ctx_functions /\ fn' = dft_fn fn /\ dft_fn_rel fn fn' /\
    ev_reachable orc initial C p d fn inst sS /\
    lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    sS.vs_current_bb = t.vs_current_bb /\
    inst_mem_ranges inst sS = inst_mem_ranges inst t /\
    sS.vs_initial_fmp = t.vs_initial_fmp
Proof
  strip_tac >> Cases_on `inst.inst_opcode = DRET`
  >- (drule_all inv_reachable_dret_exact >> strip_tac >>
      qexistsl_tac [`fn`, `t`, `bb`, `bb'`] >> metis_tac[]) >>
  drule_all inv_reachable_memory_observation >> strip_tac >>
  qexistsl_tac [`fn`, `sS`, `bb`, `bb'`] >>
  metis_tac[inv_non_dret_ranges_cong]
QED
