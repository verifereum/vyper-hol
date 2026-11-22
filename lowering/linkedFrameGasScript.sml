(* Frame gas facts used by the linked gas sufficiency proofs. *)
Theory linkedFrameGas
Ancestors
  e2eModsDefs e2eDeployModsDefs e2eDefs e2eGasSufficient frameGas
  frameOutcome vfmExecution vfmState

Theorem deploy_state_rel_add_frame_gas_mods:
  !mods exps bc am tx g es.
    deploy_state_rel_mods mods exps bc am tx es ==>
    deploy_state_rel_mods mods exps bc am tx (add_frame_gas g es)
Proof
  rw[deploy_state_rel_mods_def] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` assume_tac) >>
  qexistsl [`ctxt with msgParams updated_by (\p. p with gasLimit updated_by $+ g)`,
            `rb`, `args_bytes`] >>
  `(add_frame_gas g es).originalAccounts = es.originalAccounts` by
    (simp[add_frame_gas_def] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]) >>
  fs[add_frame_gas_wf_state, add_frame_gas_fields, add_frame_gas_bounded]
QED

Theorem call_state_rel_add_frame_gas_raises_mods:
  call_state_rel_mods mods exps runtime_bc am tx es ==>
  !g. frame_raises (add_frame_gas g es) OutOfGas <=>
      ?op. frame_inst_raises (add_frame_gas g es) OutOfGas op
Proof
  strip_tac >> gen_tac >> irule frame_raises_inst_raises >>
  qpat_x_assum `call_state_rel_mods _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [call_state_rel_mods_def, evm_state_ok_def]) >>
  simp[add_frame_gas_wf_state] >>
  drule add_frame_gas_contexts >> disch_then (qspec_then `g` strip_assume_tac) >>
  simp[]
QED
