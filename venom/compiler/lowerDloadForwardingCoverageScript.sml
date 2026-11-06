(* Forwarding endpoint expansions are singleton. Configured transport at the
   exact envelope position is already exported as ld_envelope_revert_forward
   by lowerDloadReturnAlignmentTheory; do not duplicate that boundary. *)
Theory lowerDloadForwardingCoverage
Ancestors lowerDloadReturnAlignment lowerDloadTerminalSafety
          lowerDloadSafetyRelation lowerDloadSafetyLocations
          contextCodegenRel lowerDloadSafetyAmbient venomExecSemantics
          memSafeRun venomExecProofs venomInst list

Theorem ld_forward_envelope_singleton:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ld_envelope u fn s s.vs_inst_idx X p /\ in_revert_forward fn s ==>
  LENGTH X = 1
Proof
  strip_tac >>
  `?inst. active_inst fn inst s` by
    (fs[ld_envelope_def, active_inst_def] >>
     qexists_tac `EL bi fn.fn_blocks` >> simp[MEM_EL] >> metis_tac[]) >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule_all ld_active_lookup >> metis_tac[get_instruction_def]) >>
  `inst.inst_opcode = RETURNDATACOPY \/ inst.inst_opcode = REVERT` by
    (fs[in_revert_forward_def] >> gvs[] >>
     drule_all revert_forward_at_opcode >> simp[]) >>
  `X = [inst]` by (irule ld_envelope_ordinary >> simp[] >> metis_tac[]) >>
  simp[]
QED
