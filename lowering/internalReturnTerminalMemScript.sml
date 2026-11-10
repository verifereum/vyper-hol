(* Scope-cleared internal return posts ignore registers and the instruction index. *)
Theory internalReturnTerminalMem
Ancestors
  stmtSimReturn exprLoweringProps compileEnv venomState
  vyperState

Theorem internal_return_register_terminal:
  state_rel func ce cx ee s /\ intret_vals_match tv v ws ==>
  !tail. intret_q func ce cx tv v
    ((ee with gas_obs := tail) with scopes := [])
    (IntRet <|iret_values := ws; iret_adopt_fmp := NONE|>
      (s with <|vs_vars := vs; vs_inst_idx := n|>))
Proof
  strip_tac >> gen_tac >>
  `state_rel func ce cx (ee with scopes := [])
     (s with <|vs_vars := vs; vs_inst_idx := n|>)` by
    (drule state_rel_scopes_nil >> strip_tac >>
     irule state_rel_frame >>
     simp[local_ptrs_rel_def, lookup_scopes_def, local_region_def] >>
     qexistsl_tac [`ee with scopes := []`, `s`] >> simp[] >>
     qpat_x_assum `state_rel _ _ _ _ s` mp_tac >>
     simp[state_rel_def, immutables_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `((ee with gas_obs := tail) with scopes := []) =
   ((ee with scopes := []) with gas_obs := tail)` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[intret_q_gas_obs, intret_q_def, result_rel_def]
QED
