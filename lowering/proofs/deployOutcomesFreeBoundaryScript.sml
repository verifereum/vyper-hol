(* Outcome replacement changes neither deployment observations nor code layout. *)
Theory deployOutcomesFreeBoundary
Ancestors
  ctorDeployDefs lowerDloadDefs

Theorem outcomes_update_deploy_fields[simp]:
  (s with vs_outcomes := os).vs_gas_readings = s.vs_gas_readings /\
  (s with vs_outcomes := os).vs_code = s.vs_code /\
  (s with vs_outcomes := os).vs_data_section = s.vs_data_section /\
  (code_layout_valid (s with vs_outcomes := os) = code_layout_valid s)
Proof
  simp[code_layout_valid_def]
QED

Theorem deploy_venom_result_rel_outcomes_halt[simp]:
  deploy_venom_result_rel tops runtime_bc tx src (Halt (s with vs_outcomes := os)) =
  deploy_venom_result_rel tops runtime_bc tx src (Halt s)
Proof
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >>
      simp[deploy_venom_result_rel_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> simp[deploy_venom_result_rel_def]
QED

Theorem deploy_venom_result_rel_outcomes_abort[simp]:
  deploy_venom_result_rel tops runtime_bc tx src
    (Abort reason (s with vs_outcomes := os)) =
  deploy_venom_result_rel tops runtime_bc tx src (Abort reason s)
Proof
  Cases_on `src`
  >- (rename1 `INL p` >> PairCases_on `p` >>
      simp[deploy_venom_result_rel_def]) >>
  rename1 `INR exc` >> Cases_on `exc` >> Cases_on `reason` >>
  simp[deploy_venom_result_rel_def]
QED
