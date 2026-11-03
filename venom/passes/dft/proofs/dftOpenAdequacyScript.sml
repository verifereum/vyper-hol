Theory dftOpenAdequacy
Ancestors
  dftOpenMachine gasOracleReplay venomExecSemantics venomInst stateEquiv
  dftSparseOracle list rich_list

Definition dft_open_result_eq_def:
  dft_open_result_eq r r' <=> lift_result (=) (=) (=) r r'
End

Theorem dft_open_result_eq_OK[simp]:
  dft_open_result_eq r (OK s) <=> r = OK s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_Halt[simp]:
  dft_open_result_eq r (Halt s) <=> r = Halt s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_IntRet[simp]:
  dft_open_result_eq r (IntRet ret s) <=> r = IntRet ret s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_Abort[simp]:
  dft_open_result_eq r (Abort reason s) <=> r = Abort reason s
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_open_result_eq_Error[simp]:
  dft_open_result_eq r (Error e) <=> ?e'. r = Error e'
Proof
  Cases_on `r` >> simp[dft_open_result_eq_def, lift_result_def, CONJ_COMM]
QED

Theorem dft_zero_replay_materialize:
  gas_replay_at 0 f s ==>
  dft_open_result_eq (f (dft_open_materialize xs n s))
    (dft_open_materialize_result xs n (f s))
Proof
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `DROP n xs` mp_tac) >>
  Cases_on `f s` >> Cases_on `f (s with vs_gas_readings := DROP n xs)` >>
  simp[lift_result_def, dft_open_materialize_def,
       dft_open_materialize_result_def, dft_open_result_eq_def] >>
  metis_tac[]
QED

Theorem dft_open_base_materialize:
  inst.inst_opcode <> GAS ==>
  dft_open_result_eq (step_inst_base inst (dft_open_materialize xs n s))
    (dft_open_materialize_result xs n (step_inst_base inst s))
Proof
  strip_tac >> irule dft_zero_replay_materialize >>
  simp[gas_base_non_gas]
QED

Theorem dft_open_phis_materialize:
  dft_open_result_eq (eval_phis (dft_open_materialize xs n s) insts)
    (dft_open_materialize_result xs n (eval_phis s insts))
Proof
  irule (dft_zero_replay_materialize |> SPEC_ALL |>
    Q.INST [`f` |-> `\u. eval_phis u insts`] |> BETA_RULE) >>
  simp[gas_eval_phis]
QED

Theorem dft_open_gas_materialize:
  dft_sparse_oracle a xs /\ inst.inst_opcode = GAS /\ inst.inst_outputs = [out] ==>
  step_inst_base inst (dft_open_materialize xs n s) =
    OK (dft_open_materialize xs (SUC n) (update_var out (a n) s))
Proof
  strip_tac >>
  simp[step_inst_base_def, exec_gas_def, dft_open_materialize_def] >>
  `a n = if n < LENGTH xs then EL n xs else 0w` by
    metis_tac[dft_sparse_oracle_def] >>
  Cases_on `n < LENGTH xs`
  >- (drule DROP_CONS_EL >> disch_then SUBST1_TAC >> simp[]) >>
  `DROP n xs = [] /\ DROP (SUC n) xs = []` by simp[DROP_EQ_NIL] >>
  simp[]
QED

Theorem dft_open_bad_gas_materialize:
  inst.inst_opcode = GAS /\ (!out. inst.inst_outputs <> [out]) ==>
  step_inst_base inst (dft_open_materialize xs n s) =
    Error "read0 requires single output"
Proof
  simp[step_inst_base_def, exec_gas_def] >> rpt strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED
