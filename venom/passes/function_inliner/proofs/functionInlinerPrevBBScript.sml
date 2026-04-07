(* Standalone test for run_block_no_phi_prev_bb_ok *)
Theory functionInlinerPrevBB
Ancestors
  functionInlinerCallSim functionInlinerCallSimPhiStep

open listTheory venomExecSemanticsTheory venomInstTheory venomStateTheory
     venomWfTheory functionInlinerCallSimTheory functionInlinerCallSimPhiStepTheory

Triviality run_block_no_phi_prev_bb_ok_test:
  !fuel ctx bb s s_ok p.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    bb_well_formed bb /\
    run_block fuel ctx bb s = OK s_ok ==>
    run_block fuel ctx bb (s with vs_prev_bb := p) = OK s_ok
Proof
  gen_tac >> gen_tac >> gen_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ s = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  Cases_on `get_instruction bb s.vs_inst_idx` >- simp[] >>
  rename1 `SOME inst` >>
  `inst.inst_opcode <> PHI` by (
    qpat_x_assum `EVERY _ _` mp_tac >>
    qpat_x_assum `get_instruction _ _ = _` mp_tac >>
    rw[get_instruction_def, AllCaseEqs()] >> fs[EVERY_EL]
  ) >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >- (
    rename1 `step_inst _ _ _ s = OK s_step` >>
    Cases_on `is_terminator inst.inst_opcode` >> simp[] >| [
      (* Terminator + OK: prev_bb-independent *)
      strip_tac >>
      CONV_TAC (ONCE_REWRITE_CONV [run_block_def]) >> simp[] >>
      imp_res_tac step_inst_ok_term_prev_bb_same >> simp[],
      (* Not terminator: recurse with IH *)
      strip_tac >>
      imp_res_tac step_inst_ok_nonterm_prev_bb_map >>
      qpat_x_assum `!p. ?q. _` (qspec_then `p` strip_assume_tac) >>
      CONV_TAC (ONCE_REWRITE_CONV [run_block_def]) >> simp[] >>
      qpat_x_assum `!m. m < v ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
      impl_tac >- (fs[get_instruction_def, AllCaseEqs()] >> simp[]) >>
      disch_then (qspecl_then [`bb`,
        `s_step with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`s_ok`, `q`] mp_tac) >>
      simp[]
    ]
  )
QED

val _ = export_theory();
