Theory deadStoreElimComposition
Ancestors
  deadStoreElimCertificate deadStoreElimStructure deadStoreElimEquiv
  deadStoreElimDefs passSharedProps venomWf While stateEquiv decoratedExecution

Theorem dse_iterate_certificate:
  wf_function fn /\ ssa_form fn /\ s.vs_inst_idx = 0 /\
  dse_run_certificate fn fuel ctx s r /\
  (!fn'. all_dead_stores (analysis fn') (cfg_analyze fn') FEMPTY
    (bp_analyze (cfg_analyze fn') fn') sp fn') /\
  dse_iterate analysis sp fn = SOME fn' ==>
  wf_function fn' /\ ssa_form fn' /\
  ?r'. dse_run_certificate fn' fuel ctx s r' /\
    lift_result (dse_equiv sp) dse_term_equiv (dse_equiv sp) r r'
Proof
  strip_tac >>
  qspecl_then [`\f. analysis f <> {}`, `\f. dse_single_pass (analysis f) sp f`, `fn`]
    mp_tac (OWHILE_INV_IND |> INST_TYPE [alpha |-> ``:ir_function``]
      |> Q.INST [`P` |-> `\f. wf_function f /\ ssa_form f /\
        ?v. dse_run_certificate f fuel ctx s v /\
          lift_result (dse_equiv sp) dse_term_equiv (dse_equiv sp) r v`]) >>
  impl_tac
  >- (conj_tac
      >- (simp[] >> qexists_tac `r` >> simp[] >>
          Cases_on `r` >> simp[lift_result_def, dse_equiv_refl]) >>
      rpt gen_tac >> simp[] >> strip_tac >>
      `wf_function (dse_single_pass (analysis x) sp x)` by
        (irule dse_single_pass_preserves_wf >> simp[]) >>
      `ssa_form (dse_single_pass (analysis x) sp x)` by
        (irule dse_single_pass_preserves_ssa >> simp[]) >>
      qpat_assum `!f. all_dead_stores _ _ _ _ _ f`
        (qspec_then `x` assume_tac) >>
      simp[] >> drule_all dse_certificate_round >> strip_tac >>
      goal_assum (drule_at Any) >>
      metis_tac[lift_result_dse_term_trans]) >>
  disch_then (qspec_then `fn'` mp_tac) >> fs[dse_iterate_def]
QED

Theorem dse_function_space_certificate:
  wf_function fn /\ ssa_form fn /\ s.vs_inst_idx = 0 /\
  dse_run_certificate fn fuel ctx s r /\
  (!fn'. all_dead_stores (analysis_fn sp fn') (cfg_analyze fn') FEMPTY
    (bp_analyze (cfg_analyze fn') fn') sp fn') ==>
  wf_function (dse_function_space analysis_fn sp fn) /\
  ssa_form (dse_function_space analysis_fn sp fn) /\
  ?r'. dse_run_certificate (dse_function_space analysis_fn sp fn) fuel ctx s r' /\
    lift_result (dse_equiv sp) dse_term_equiv (dse_equiv sp) r r'
Proof
  strip_tac >>
  Cases_on `dse_iterate (analysis_fn sp) sp fn`
  >- (simp[dse_function_space_def] >>
      `wf_function (clear_nops_function fn)` by
        (irule clear_nops_function_preserves_wf >> simp[]) >>
      `ssa_form (clear_nops_function fn)` by
        (irule clear_nops_function_preserves_ssa >> simp[]) >>
      simp[] >> drule_all dse_certificate_clear_nops >>
      metis_tac[lift_result_dse_equiv_term]) >>
  drule_all dse_iterate_certificate >> strip_tac >>
  simp[dse_function_space_def] >>
  `wf_function (clear_nops_function x)` by
    (irule clear_nops_function_preserves_wf >> simp[]) >>
  `ssa_form (clear_nops_function x)` by
    (irule clear_nops_function_preserves_ssa >> simp[]) >>
  simp[] >> drule_all dse_certificate_clear_nops >> strip_tac >>
  goal_assum (drule_at Any) >>
  metis_tac[lift_result_dse_term_trans, lift_result_dse_equiv_term]
QED

Theorem dse_function_certificate:
  wf_function fn /\ ssa_form fn /\ s.vs_inst_idx = 0 /\
  dse_run_certificate fn fuel ctx s r /\
  (!sp fn'. all_dead_stores (analysis_fn sp fn') (cfg_analyze fn') FEMPTY
    (bp_analyze (cfg_analyze fn') fn') sp fn') ==>
  wf_function (dse_function analysis_fn fn) /\
  ssa_form (dse_function analysis_fn fn) /\
  ?r'. dse_run_certificate (dse_function analysis_fn fn) fuel ctx s r' /\
    lift_result dse_all_equiv dse_term_equiv dse_all_equiv r r'
Proof
  strip_tac >>
  map_every (fn sp =>
    qpat_assum `!sp f. all_dead_stores _ _ _ _ sp f`
      (qspec_then sp assume_tac) >>
    drule_all (dse_function_space_certificate |> Q.INST [`sp` |-> sp]) >>
    strip_tac)
    [`AddrSp_Memory`, `AddrSp_Storage`, `AddrSp_Transient`] >>
  simp[dse_function_def] >>
  goal_assum (drule_at Any) >>
  imp_res_tac lift_result_dse_term_to_all >>
  metis_tac[lift_result_dse_all_term_trans]
QED
