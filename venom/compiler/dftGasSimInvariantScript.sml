Theory dftGasSimInvariant
Ancestors
  dftGasSimBoundary dftGasOracleDefs dftRunRel sccpCorrectnessProofs
  venomExecSemantics venomExecProofs venomState venomInst

Theorem ev_setup_callee_dominators:
  setup_callee fn args s = SOME t ==> strict_dom_vars_defined fn t
Proof
  strip_tac >> irule strict_dom_vars_defined_entry >>
  gvs[setup_callee_def, AllCaseEqs(), fn_entry_label_def, entry_block_def]
QED

Theorem ev_step_labels:
  ev_step orc p d fuel C inst s = OK t ==> t.vs_labels = s.vs_labels
Proof
  Cases_on `inst.inst_opcode = GAS`
  >- (simp[ev_step_gas, ev_gas_def] >>
      Cases_on `inst.inst_outputs` >> simp[] >>
      rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
      simp[update_var_def] >> strip_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once ev_step_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >>
      `!pairs st. (FOLDL (\st' (out,value). update_var out value st') st pairs).vs_labels = st.vs_labels` by
        (Induct >> simp[] >> Cases >> simp[update_var_def]) >>
      gvs[bind_outputs_def, AllCaseEqs()] >>
      simp[adopt_return_fmp_def, merge_callee_state_def] >>
      Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  simp[Once ev_step_def] >> strip_tac >>
  `step_inst fuel C inst s = OK t` by simp[step_inst_non_invoke] >>
  metis_tac[step_inst_preserves_labels_always]
QED

Theorem ev_suffix_labels:
  !xs s t. ev_suffix orc p d fuel C xs s = OK t ==>
    t.vs_labels = s.vs_labels
Proof
  Induct >> simp[ev_suffix_def] >> rpt gen_tac >>
  Cases_on `ev_step orc p d fuel C h s` >> simp[] >>
  drule ev_step_labels >> strip_tac >>
  IF_CASES_TAC
  >- (IF_CASES_TAC >> simp[] >> strip_tac >> gvs[]) >>
  simp[] >> strip_tac >> first_x_assum drule >> simp[]
QED

Theorem ev_block_labels:
  ev_block orc p d fuel C bb s = OK t ==> t.vs_labels = s.vs_labels
Proof
  mp_tac (ev_suffix_block |> Q.INST [`ctx` |-> `C`]) >>
  disch_then (qspecl_then [`DROP s.vs_inst_idx bb.bb_instructions`, `s`, `bb`] mp_tac) >>
  simp[] >> metis_tac[ev_suffix_labels]
QED

Theorem ctx_labels_bound_ev_step:
  ctx_labels_bound C s.vs_labels /\ ev_step orc p d fuel D inst s = OK t ==>
    ctx_labels_bound C t.vs_labels
Proof
  metis_tac[ev_step_labels]
QED
