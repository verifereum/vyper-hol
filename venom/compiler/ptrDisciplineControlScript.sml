(* Small control and provenance interfaces for reachable frame invariants. *)
Theory ptrDisciplineControl
Ancestors
  ptrDiscipline venomExecSemantics venomExecProofs venomInstProofs1 contextCodegenRel
  venomWfProps venomState list finite_map

Theorem step_prov_terminator:
  inst_wf inst /\ is_terminator inst.inst_opcode ==>
  step_prov PG G inst t = G
Proof
  strip_tac >> `inst.inst_outputs = []` by metis_tac[terminator_no_outputs] >>
  simp[step_prov_def, set_prov_def, DRESTRICT_UNIV]
QED

Theorem enters_block_current_bb:
  enters_block fn s t ==> t.vs_current_bb = s.vs_current_bb
Proof
  rw[enters_block_def] >> simp[] >> drule eval_phis_preserves_current_bb >> simp[]
QED

Theorem bind_return_current_bb:
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s e)) = SOME t ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `t.vs_current_bb = (adopt_return_fmp ret (merge_callee_state s e)).vs_current_bb` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def]
QED
