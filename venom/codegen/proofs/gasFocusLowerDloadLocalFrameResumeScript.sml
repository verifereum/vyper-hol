(* A frame return restores the saved callers at their next instruction.
   This uses a local IntRet step, not a completed callee evaluation. *)
Theory gasFocusLowerDloadLocalFrameResume
Ancestors
  lowerDloadSafetyLocations lowerDloadDefs ptrDiscipline
  o1LowerDloadRunnerBoundary o1LowerDloadJointRestore
  venomExecSemantics venomState venomInst finite_map pred_set list

Theorem ld_focus_local_frame_resume:
  ALL_DISTINCT (MAP (\b. b.bb_label) c.cf_fn.fn_blocks) /\
  d.cf_fn = FST (lower_dload_function_supply supply c.cf_fn) /\
  c.cf_state.vs_current_bb = d.cf_state.vs_current_bb /\
  ld_envelope supply c.cf_fn c.cf_state c.cf_state.vs_inst_idx [c.cf_inst] p /\
  d.cf_state.vs_inst_idx = p /\
  c.cf_inst.inst_outputs = d.cf_inst.inst_outputs /\
  frame_reachable vs0 C (c::stk) PG G tn fn ri s /\
  active_inst fn ri s /\ ri.inst_opcode = RET /\
  step_inst sf C ri s = IntRet rs se /\
  step_inst tf C' ri t = IntRet rt te /\
  rs.iret_values = rt.iret_values /\
  rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
  bind_outputs d.cf_inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state d.cf_state te)) = SOME q /\
  active_inst d.cf_fn ti (q with vs_inst_idx := SUC d.cf_state.vs_inst_idx) ==>
  ?sr next Y.
    bind_outputs c.cf_inst.inst_outputs rs.iret_values
      (adopt_return_fmp rs (merge_callee_state c.cf_state se)) = SOME sr /\
    active_inst c.cf_fn next (sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx) /\
    ld_envelope supply c.cf_fn (sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (SUC c.cf_state.vs_inst_idx) Y (SUC p) /\
    0 < LENGTH Y /\ ti = EL 0 Y /\
    frame_reachable vs0 C stk c.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      c.cf_fn next (sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx) /\
    sr.vs_gas_readings = s.vs_gas_readings /\
    q.vs_gas_readings = t.vs_gas_readings /\
    (se.vs_gas_readings = te.vs_gas_readings ==> sr.vs_gas_readings = q.vs_gas_readings)
Proof
  strip_tac >>
  `?sr. bind_outputs c.cf_inst.inst_outputs rs.iret_values
          (adopt_return_fmp rs (merge_callee_state c.cf_state se)) = SOME sr` by
    ((qpat_assum `bind_outputs _ _ _ = SOME q` mp_tac >>
     simp[bind_outputs_def] >> (gvs[bind_outputs_def]))) >>
  `sr.vs_current_bb = c.cf_state.vs_current_bb /\
   q.vs_current_bb = d.cf_state.vs_current_bb` by metis_tac[ld_invoke_bind_control] >>
  `?next Y.
    active_inst c.cf_fn next (sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx) /\
    ld_envelope supply c.cf_fn (sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx)
      (SUC c.cf_state.vs_inst_idx) Y (SUC p) /\ 0 < LENGTH Y /\ ti = EL 0 Y` by
    (simp[arithmeticTheory.ADD1] >>
     irule (SRULE [arithmeticTheory.ADD1]
       (Q.INST [`X` |-> `[c.cf_inst]`] (SPEC_ALL ld_envelope_successor_head))) >>
     goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD1] >>
     qexistsl_tac [`c`, `q with vs_inst_idx := SUC d.cf_state.vs_inst_idx`, `c.cf_state`] >>
     gs[arithmeticTheory.ADD1]) >>
  `frame_reachable vs0 C stk c.cf_params
      (DRESTRICT c.cf_prov (COMPL (set c.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT c.cf_tvar (COMPL (set c.cf_inst.inst_outputs)))
      c.cf_fn next (sr with vs_inst_idx := SUC c.cf_state.vs_inst_idx)` by
    (drule frame_reachable_ret >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`sr`, `next`, `Y`] >> asm_rewrite_tac[] >>
  `se = s /\ te = t` by metis_tac[ld_ret_endpoint] >>
  `bind_outputs c.cf_inst.inst_outputs rs.iret_values (merge_callee_state c.cf_state se) = SOME sr /\
   bind_outputs d.cf_inst.inst_outputs rt.iret_values (merge_callee_state d.cf_state te) = SOME q` by
    gs[adopt_return_fmp_def] >>
  qpat_assum `bind_outputs _ _ (merge_callee_state _ _) = SOME sr`
    (assume_tac o MATCH_MP ld_bind_outputs_vars_only) >>
  qpat_assum `bind_outputs _ _ (merge_callee_state _ _) = SOME q`
    (assume_tac o MATCH_MP ld_bind_outputs_vars_only) >>
  ntac 2 (pop_assum (fn th => once_rewrite_tac[th])) >> simp[merge_callee_state_def]
QED
