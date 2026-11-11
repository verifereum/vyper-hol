Theory lowerDloadPtrDynamicSupport
Ancestors ptrDiscipline venomExecSemantics venomState venomInstProps venomExecProps contextCodegenRel finite_map list

Theorem dload_phis_prov_defined:
  !is s s' G.
    eval_phis s is = OK s' /\
    (!v. v IN FDOM G ==> lookup_var v s <> NONE) ==>
    !v. v IN FDOM (phis_prov s.vs_prev_bb G is) ==>
        lookup_var v s' <> NONE
Proof
  Induct_on `is` >- simp[eval_phis_def, phis_prov_def] >>
  rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[eval_phis_def, phis_prov_def] >>
      Cases_on `eval_one_phi s h` >> simp[] >>
      PairCases_on `x` >>
      Cases_on `eval_phis s is` >> simp[] >>
      rpt strip_tac >> gvs[] >>
      `h.inst_outputs = [x0]` by
        (gvs[eval_one_phi_def, AllCaseEqs()]) >>
      gvs[set_prov_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          AllCaseEqs()] >>
      Cases_on `phi_prov s.vs_prev_bb G h` >>
      gvs[FDOM_DRESTRICT] >>
      first_x_assum drule >> simp[] >> metis_tac[]) >>
  simp[eval_phis_def, phis_prov_def] >> metis_tac[]
QED

Theorem dload_prov_output_defined:
  step_inst fuel C i s = OK s' /\
  i.inst_outputs = [v] /\ out_prov PG G i s' = SOME site ==>
  lookup_var v s' <> NONE
Proof
  rpt strip_tac >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, exec_alloca_def,
          AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  Cases_on `i.inst_opcode = DALLOCA`
  >- (gvs[out_prov_def, AllCaseEqs()]) >>
  Cases_on `i.inst_opcode = PARAM`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
          update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `i.inst_opcode = ADD \/ i.inst_opcode = SUB \/
   i.inst_opcode = ASSIGN` by (gvs[out_prov_def, AllCaseEqs()]) >>
  gvs[step_inst_non_invoke, step_inst_base_def] >>
  gvs[exec_pure1_def, exec_pure2_def, AllCaseEqs()] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem dload_step_prov_defined:
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  step_inst fuel C i s = OK s' /\
  (!v. v IN FDOM G ==> lookup_var v s <> NONE) ==>
  !v. v IN FDOM (step_prov PG G i s') ==> lookup_var v s' <> NONE
Proof
  rpt strip_tac >>
  Cases_on `i.inst_outputs` >>
  gvs[step_prov_def, set_prov_def, FDOM_DRESTRICT] >-
    metis_tac[step_preserves_non_output_vars, MEM] >>
  rename1 `i.inst_outputs = out::outs` >>
  Cases_on `outs` >>
  Cases_on `out_prov PG G i s'` >>
  gvs[step_prov_def, set_prov_def, FDOM_DRESTRICT] >>
  metis_tac[dload_prov_output_defined, step_preserves_non_output_vars, MEM]
QED

Theorem dload_entry_prov_defined:
  enters_block fn s s' /\
  (!v. v IN FDOM G ==> lookup_var v s <> NONE) ==>
  !v. v IN FDOM (entry_prov fn s G) ==> lookup_var v s' <> NONE
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  gvs[entry_prov_def, lookup_var_def] >>
  drule dload_phis_prov_defined >> simp[lookup_var_def] >> metis_tac[]
QED

Theorem dload_terminator_prov_defined:
  is_terminator i.inst_opcode /\ step_inst fuel C i s = OK s' /\
  (!v. v IN FDOM G ==> lookup_var v s <> NONE) ==>
  !v. v IN FDOM G ==> lookup_var v s' <> NONE
Proof
  metis_tac[step_terminator_preserves_vars]
QED

Theorem dload_fold_outputs_unwritten:
  !pairs s v. ~MEM v (MAP FST pairs) ==>
    lookup_var v (FOLDL (\s' (out,value). update_var out value s') s pairs) =
    lookup_var v s
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem dload_return_prov_defined:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state s t)) = SOME s' /\
  (!v. v IN FDOM G ==> lookup_var v s <> NONE) ==>
  !v. v IN FDOM (DRESTRICT G (COMPL (set outs))) ==>
    lookup_var v s' <> NONE
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[FDOM_DRESTRICT] >>
  `MAP FST (ZIP (outs,vals)) = outs` by simp[MAP_ZIP] >>
  `~MEM v (MAP FST (ZIP (outs,vals)))` by simp[] >>
  drule dload_fold_outputs_unwritten >>
  disch_then (qspec_then `adopt_return_fmp ret (merge_callee_state s t)` mp_tac) >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[lookup_var_def, adopt_return_fmp_def, merge_callee_state_def] >>
  metis_tac[lookup_var_def]
QED

Theorem dload_frame_prov_defined:
  !vs0 C stk PG G tn fn inst s.
  frame_reachable vs0 C stk PG G tn fn inst s ==>
  (!v. v IN FDOM G ==> lookup_var v s <> NONE) /\
  (!c v. MEM c stk /\ v IN FDOM c.cf_prov ==>
         lookup_var v c.cf_state <> NONE)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[lookup_var_def] >>
      metis_tac[dload_step_prov_defined, lookup_var_def])
  >- (rpt strip_tac >>
      metis_tac[dload_entry_prov_defined, dload_terminator_prov_defined])
  >- (simp[] >> rpt strip_tac >> gvs[] >> metis_tac[])
  >> rpt strip_tac >> gvs[lookup_var_def] >>
  metis_tac[dload_return_prov_defined, lookup_var_def]
QED
