Theory dftEvmExtractionProbe
Ancestors
  dftEvmConstructedState venomExecSemantics vfmExecution vfmDomainCollection
  vfmRunWithinFrame

(* The actual CREATE constructor does not enforce a partial domain. *)
Theorem dft_probe_create_collect:
  (make_venom_create_state s addr gas value code).msdomain = Collect empty_domain
Proof
  simp[make_venom_create_state_def]
QED

(* Collection mode cannot cause OutsideDomain, even inside a child frame. *)
Theorem dft_probe_collect_step_no_domain_abort:
  s.msdomain = Collect d /\ step s = (INR (SOME (OutsideDomain x)), t) ==> F
Proof
  strip_tac >>
  mp_tac step_computes_minimal_domain >>
  rewrite_tac[computes_minimal_domain_def] >>
  disch_then (qspecl_then [`s`, `INR (SOME (OutsideDomain x))`, `t`, `d`] mp_tac) >>
  simp[]
QED

Theorem dft_probe_collect_step_stays_collect:
  s.msdomain = Collect d /\ step s = (r,t) ==> ?d'. t.msdomain = Collect d'
Proof
  metis_tac[step_preserves_collect]
QED

(* Nested precompile calls cannot reach the dispatcher's Impossible default. *)
Theorem dft_probe_precompile_no_abort:
  s.contexts <> [] /\ fIN a precompile_addresses /\
  dispatch_precompiles a s = (INR e,t) ==> ~vfm_abort e
Proof
  metis_tac[dispatch_precompiles_inr_not_reverted_not_abort]
QED

Theorem dft_probe_pop_gas_guard:
  s.contexts = (callee, rb) :: parent :: rest /\
  callee.msgParams.gasLimit - callee.gasUsed <= (FST parent).gasUsed /\
  pop_and_incorporate_context success s = (r,t) ==>
  r = INL ()
Proof
  strip_tac >> Cases_on `parent` >>
  gvs[pop_and_incorporate_context_def, get_gas_left_def,
      pop_context_def, unuse_gas_def, get_current_context_def,
      set_current_context_def, set_rollback_def, push_logs_def,
      update_gas_refund_def, bind_def, ignore_bind_def, return_def,
      assert_def, fail_def] >>
  Cases_on `success` >>
  gvs[bind_def, ignore_bind_def, get_current_context_def,
      set_current_context_def, set_rollback_def, return_def]
QED

(* Residual invariant audit (not a reachable-abort witness):
   - step_create charges cappedGas before proceed_create installs a child
     whose gasLimit is cappedGas (vfmExecution, step_create/proceed_create).
   - step_call charges static_gas + dynamicGas + mx.cost before proceed_call
     installs gasLimit = stipend. call_gas returns (gas + otherCost,
     gas + call_stipend) for positive value: the extra stipend requires the
     positive-value cost, not merely equality of gas charged and child limit.
   - gas_stack_ok_parent_has_child_unused (vfmHandleStep) supplies exactly
     the pop guard without accounts assumptions. same_frame_rel preservation
     and handle_create_preserves_gas_stack_ok are also accounts-independent.
   - inner_push_preserves_gas_stack_ok and step_preserves_gas_stack_ok
     (vfmRunCall) require wf_state, hence do not directly supply preservation
     from arbitrary Venom accounts. No accounts-independent full execution
     invariant is established here. No counterexample is claimed.
*)
