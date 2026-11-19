Theory dftGasSourcePrefix
Ancestors
  dftGasFromListTraceDefs dftGasFromListReadings
  gasEvents gasCount gasOracleReplay dftIndexedExec dftRunRel dftBlockSim
  removeUnusedGasProofs venomExecProofs venomExecSemantics venomState venomInst
  list rich_list option arithmetic

Theorem noninvoke_prefix_trace_keys:
  !pre s bb u gs tail fuel C func p d.
    DROP s.vs_inst_idx bb.bb_instructions = pre /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) pre /\
    LENGTH gs = LENGTH (FILTER (\i. i.inst_opcode = GAS) pre) /\
    FOLDR (dft_exec_cons fuel C) OK pre
      (s with vs_gas_readings := gs ++ tail) = OK u ==>
    dftGasFromListTraceDefs$trace_gas
      (dftGasFromListTraceDefs$trace_block p d fuel C func bb
        (s with vs_gas_readings := gs ++ tail)) =
    ZIP (MAP (\i. (p,d,i.inst_id))
      (FILTER (\i. i.inst_opcode = GAS) pre), gs)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[DROP_EQ_NIL] >>
      simp[Once trace_defs, get_instruction_def, trace_gas_def]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
      (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[LENGTH_DROP]) >>
  `EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = pre` by
    gvs[rich_listTheory.DROP_CONS_EL] >>
  fs[EVERY_DEF, dftIndexedExecTheory.dft_exec_cons_def] >>
  Cases_on `step_inst fuel C h (s with vs_gas_readings := gs ++ tail)` >> gvs[] >>
  simp[Once trace_defs, get_instruction_def, trace_step_noninvoke] >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = GAS`
  >- (drule_all dftBlockSimTheory.step_inst_ok_gas >> strip_tac >>
      Cases_on `gs` >> fs[update_var_def] >>
      first_x_assum (qspecl_then
        [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `u`, `t`, `tail`,
         `fuel`, `C`, `func`, `p`, `d`] mp_tac) >>
      simp[visit_gas_def]) >>
  drule_all dft_nonconsuming_ok_readings >> strip_tac >>
  first_x_assum (qspecl_then
    [`v with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `u`, `gs`, `tail`,
     `fuel`, `C`, `func`, `p`, `d`] mp_tac) >>
  `v with vs_gas_readings := gs ++ tail = v` by
    simp[venom_state_component_equality] >>
  simp[visit_gas_def]
QED

