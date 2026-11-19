Theory dftGasNativePrefixReplay
Ancestors
  dftGasFromListReplay dftGasFromListRestore dftGasFromListTraceDefs
  dftGasInvPrefixRun dftPacketNativePrefixBoundary dftIndexedExec gasEvents venomExecSemantics
  venomInst venomState rich_list arithmetic

Theorem native_prefix_trace_to_oracle[local]:
  !n s u.
    s.vs_inst_idx + n <= LENGTH bb.bb_instructions /\
    inv_ev_trace orc p d fuel C
      (TAKE n (DROP s.vs_inst_idx bb.bb_instructions)) s u ==>
    inv_ev_prefix orc p d C bb n s u
Proof
  Induct >- simp[dftGasInvResidualTraceTheory.inv_ev_trace_def] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  `TAKE (SUC n) (DROP s.vs_inst_idx bb.bb_instructions) =
    EL s.vs_inst_idx bb.bb_instructions ::
      TAKE n (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    simp[Once DROP_CONS_EL] >>
  gvs[dftGasInvResidualTraceTheory.inv_ev_trace_def] >>
  simp[inv_ev_prefix_suc, get_instruction_def] >>
  goal_assum (drule_at Any) >>
  first_x_assum irule >> simp[] >>
  qpat_assum `SUC n + s.vs_inst_idx <= _` mp_tac >> decide_tac
QED

(* Replay the completed prefix, excluding its next instruction and child.
   Step trace_replay and restore_rel_cases preserve the same native endpoint
   after normalizing readings. An induction over q follows the clipped trace;
   whole clipped-block replay instead ends in artificial fallthrough Error.
   q = 0 and exhausted native readings are included. Earlier completed child
   traces are included; no current-child completion is required. *)
Theorem native_prefix_oracle:
  !fuel C func bb s u p d q orc rs.
    s.vs_inst_idx + q <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) /\
    FOLDR (dft_exec_cons fuel C) OK
      (TAKE q (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u /\
    trace_agrees orc
      (dftGasFromListTraceDefs$trace_block p d fuel C func
        (bb with bb_instructions :=
          TAKE (s.vs_inst_idx + q) bb.bb_instructions) s) ==>
    inv_ev_prefix orc p d C bb q
      (s with vs_gas_readings := rs)
      (u with vs_gas_readings := rs)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dft_packet_native_prefix_trace >> strip_tac >>
  irule native_prefix_trace_to_oracle >> simp[] >>
  qexists_tac `fuel` >> simp[]
QED
