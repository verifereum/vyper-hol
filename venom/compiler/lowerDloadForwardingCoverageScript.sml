(* Forwarding endpoint expansions are singleton. Configured transport at the
   exact envelope position is already exported as ld_envelope_revert_forward
   by lowerDloadReturnAlignmentTheory; do not duplicate that boundary. *)
Theory lowerDloadForwardingCoverage
Ancestors lowerDloadReturnAlignment lowerDloadTerminalSafety
          lowerDloadSafetyRelation lowerDloadSafetyLocations
          contextCodegenRel lowerDloadSafetyAmbient venomExecSemantics
          memSafeRun venomExecProofs venomInst list
          stepWriteFootprintForward unitMemInv unitTransformDefs
          codegenRel venomState
Libs lowerDloadForwardingPackageLib

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

Theorem ld_forward_current_raw:
  ^ld_forward ctx fn inst s ==> raw_mem_ok ctx fn inst s
Proof
  simp[] >> rpt strip_tac >> irule ld_forward_suffix_raw >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem ld_forward_opcode:
  ^ld_forward ctx fn inst s ==>
  inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY \/
  inst.inst_opcode = REVERT
Proof
  simp[] >> rpt strip_tac >>
  Cases_on `s.vs_inst_idx = i`
  >- gvs[revert_forward_pair_def] >>
  Cases_on `s.vs_inst_idx = j`
  >- gvs[revert_forward_pair_def] >>
  disj1_tac >> gvs[revert_forward_pair_def] >> first_x_assum irule >>
  qexists_tac `s.vs_inst_idx` >> simp[] >> decide_tac
QED

Theorem ld_forward_no_invoke:
  ^ld_forward ctx fn inst s ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> drule ld_forward_opcode >> simp[] >> strip_tac >> simp[]
QED

Theorem ld_forward_no_terminator_ok:
  ^ld_forward ctx fn inst s /\ is_terminator inst.inst_opcode ==>
  step_inst fuel ctx inst s <> OK t
Proof
  strip_tac >> drule ld_forward_opcode >> strip_tac >>
  gvs[is_terminator_def] >> metis_tac[step_revert_no_normal]
QED

Theorem ld_forward_next:
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  ^ld_forward ctx fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst s = OK u /\
  active_inst fn inst' (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ^ld_forward ctx fn inst' (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY` by
    (drule ld_forward_opcode >> strip_tac >> gvs[is_terminator_def]) >>
  `u.vs_current_bb = s.vs_current_bb` by
    (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
         update_var_def, write_memory_with_expansion_def]) >>
  fs[] >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (irule ld_forward_suffix_step_frontier >> metis_tac[]) >>
  `s.vs_inst_idx < j` by
    (Cases_on `s.vs_inst_idx = j` >> gvs[revert_forward_pair_def] >>
     decide_tac) >>
  drule_all ld_active_lookup >> simp[] >> strip_tac >>
  qexistsl_tac [`i`, `j`] >>
  gvs[get_instruction_def]
QED
