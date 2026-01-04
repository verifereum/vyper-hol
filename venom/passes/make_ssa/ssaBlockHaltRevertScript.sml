(*
 * SSA Construction Block-Level: Halt/Revert Equivalence
 *
 * TOP-LEVEL:
 *   - step_inst_halt_ssa_equiv
 *   - step_inst_revert_ssa_equiv
 *
 * These are corollaries of step_inst_result_ssa_equiv for non-PHI,
 * single-output instructions.
 *)

Theory ssaBlockHaltRevert
Ancestors
  ssaBlockStep ssaStateEquiv

(* KEY LEMMA: Non-PHI instruction step that returns Halt. *)
Theorem step_inst_halt_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_opcode <> PHI /\
    LENGTH inst.inst_outputs <= 1 /\
    step_inst inst s_orig = Halt r_orig ==>
    ?r_ssa.
      step_inst inst_ssa s_ssa = Halt r_ssa /\
      ssa_state_equiv vm r_orig r_ssa
Proof
  rpt strip_tac >>
  `ssa_result_equiv vm (step_inst inst s_orig) (step_inst inst_ssa s_ssa)` by
    (irule step_inst_result_ssa_equiv >> simp[]) >>
  Cases_on `step_inst inst_ssa s_ssa` >| [
    gvs[ssa_result_equiv_def],
    (rename1 `Halt r_ssa` >>
     qexists_tac `r_ssa` >> gvs[ssa_result_equiv_def]),
    gvs[ssa_result_equiv_def],
    gvs[ssa_result_equiv_def]
  ]
QED

(* KEY LEMMA: Non-PHI instruction step that returns Revert. *)
Theorem step_inst_revert_ssa_equiv:
  !inst inst_ssa s_orig s_ssa vm r_orig.
    ssa_state_equiv vm s_orig s_ssa /\
    inst_ssa_compatible vm inst inst_ssa /\
    inst.inst_opcode <> PHI /\
    LENGTH inst.inst_outputs <= 1 /\
    step_inst inst s_orig = Revert r_orig ==>
    ?r_ssa.
      step_inst inst_ssa s_ssa = Revert r_ssa /\
      ssa_state_equiv vm r_orig r_ssa
Proof
  rpt strip_tac >>
  `ssa_result_equiv vm (step_inst inst s_orig) (step_inst inst_ssa s_ssa)` by
    (irule step_inst_result_ssa_equiv >> simp[]) >>
  Cases_on `step_inst inst_ssa s_ssa` >| [
    gvs[ssa_result_equiv_def],
    gvs[ssa_result_equiv_def],
    (rename1 `Revert r_ssa` >>
     qexists_tac `r_ssa` >> gvs[ssa_result_equiv_def]),
    gvs[ssa_result_equiv_def]
  ]
QED
