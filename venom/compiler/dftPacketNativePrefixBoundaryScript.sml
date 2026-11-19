Theory dftPacketNativePrefixBoundary
Ancestors
  dftGasFromListReplay dftGasFromListRestore dftGasFromListTraceDefs
  dftGasInvResidualTrace dftIndexedExec gasEvents venomExecSemantics
  venomInst venomState rich_list arithmetic

(* Successful native prefixes replay at the original fuel, including the
   native instruction-index increments and every non-gas state field. *)
Theorem dft_packet_native_prefix_trace:
  !fuel C func bb s u p d q orc rs.
    s.vs_inst_idx + q <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u /\
    trace_agrees orc
      (dftGasFromListTraceDefs$trace_block p d fuel C func
        (bb with bb_instructions := TAKE (s.vs_inst_idx + q) bb.bb_instructions) s)
    ==>
    inv_ev_trace orc p d fuel C
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions))
      (s with vs_gas_readings := rs)
      (u with vs_gas_readings := rs)
Proof
  Induct_on `q`
  >- (simp[inv_ev_trace_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `TAKE (SUC q) (DROP s.vs_inst_idx bb.bb_instructions) =
    EL s.vs_inst_idx bb.bb_instructions ::
      TAKE q (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    (simp[Once DROP_CONS_EL]) >>
  gvs[] >>
  Cases_on `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s` >>
  gvs[dft_exec_cons_def] >>
  rename1 `step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s = OK t` >>
  `get_instruction (bb with bb_instructions :=
      TAKE (s.vs_inst_idx + SUC q) bb.bb_instructions) s.vs_inst_idx =
    SOME (EL s.vs_inst_idx bb.bb_instructions)` by
    (simp[get_instruction_def, EL_TAKE]) >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`p`, `fuel`, `func`, `d`, `C`] assume_tac) >>
  gvs[dftGasFromListReplayBoundaryTheory.trace_agrees_cons,
      dftGasFromListReplayBoundaryTheory.trace_agrees_append] >>
  `restore_rel rs
    (step_inst fuel C (EL s.vs_inst_idx bb.bb_instructions) s)
    (dftGasOracleDefs$ev_step orc p d fuel C
      (EL s.vs_inst_idx bb.bb_instructions) (s with vs_gas_readings := rs))` by
    (irule (cj 1 trace_replay) >>
     qexists_tac `func` >>
     simp[dftGasFromListReplayBoundaryTheory.trace_agrees_cons]) >>
  gvs[restore_rel_cases] >>
  simp[Once inv_ev_trace_def] >>
  first_x_assum (qspecl_then
    [`fuel`, `C`, `func`, `bb`, `t with vs_inst_idx := SUC s.vs_inst_idx`]
    mp_tac) >>
  simp[ADD_CLAUSES] >>
  disch_then irule >> gvs[ADD_CLAUSES]
QED

Theorem dft_packet_inv_ev_trace_unique:
  inv_ev_trace orc p d fuel C pre s u /\
  inv_ev_trace orc p d fuel C pre s v ==> u = v
Proof
  qid_spec_tac `s` >> Induct_on `pre` >>
  simp[inv_ev_trace_def] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
