(* Exact successful DFT swaps, including external-call instructions. *)
Theory dftSuccessSwap
Ancestors
  dftGuards dftPermSim dftIndexedExec venomCallOracleDefs
  venomExecSemantics venomEffects venomInst venomState list
Libs
  stepInstBaseLib

Theorem dft_extract_result_fmp[local]:
  extract_venom_result s value off sz result = SOME (v,t) ==>
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac `case res of INL _ => _ | INR NONE => _ | INR (SOME _) => _` >>
  Cases_on `res` >> gvs[AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `case opt of NONE => _ | SOME _ => _` >>
  Cases_on `opt` >> gvs[]
QED

Theorem dft_external_ok_fmp_fields[local]:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_fmp = s.vs_fmp /\ t.vs_initial_fmp = s.vs_initial_fmp
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  fs[is_ext_call_op_def] >> fs[Once step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  with_opcode_clause simp >>
  simp[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  drule dft_extract_result_fmp >> simp[update_var_def]
QED

Theorem dft_external_ok_fmp:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  metis_tac[dft_external_ok_fmp_fields]
QED

Theorem dft_external_ok_initial_fmp:
  is_ext_call_op i.inst_opcode /\ step_inst fuel C i s = OK t ==>
  t.vs_initial_fmp = s.vs_initial_fmp
Proof
  metis_tac[dft_external_ok_fmp_fields]
QED
