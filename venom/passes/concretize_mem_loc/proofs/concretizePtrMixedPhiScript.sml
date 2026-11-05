Theory concretizePtrMixedPhi
Ancestors
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueSelection
  concretizePtrValueTransport ptrDiscipline unitShapeDefs
  venomExecSemantics venomState finite_map list

Theorem ptr_mixed_phis_token[local]:
  !insts s s'. eval_phis s insts = OK s' ==>
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode <> PHI` >> simp[] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def] >>
  metis_tac[]
QED

Theorem ptr_mixed_eval_phis:
  !insts t'.
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_core_shared s t /\
  s.vs_prev_bb = t.vs_prev_bb /\ retpc_shape_ok f /\
  EVERY (\i. MEM i (fn_insts f) /\ inst_wf i) insts /\
  eval_phis t insts = OK t' ==>
  ?s'. eval_phis s insts = OK s' /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG insts)
      (tn with t_var := phis_taint s.vs_prev_bb tn insts) f g s' t' /\
    ptr_core_shared s' t'
Proof
  Induct
  >- (simp[eval_phis_def, phis_prov_def, phis_taint_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode <> PHI`
  >- (gvs[eval_phis_def, phis_prov_def, phis_taint_def] >>
      qexists_tac `s` >> simp[]) >>
  `s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels` by
    fs[ptr_core_shared_def, ptr_shared_fields_def] >>
  `OPTREL (\(out,sv) (out',tv). out = out' /\
      if retpc_var f out then
        sv = s.vs_return_pc_token /\ tv = t.vs_return_pc_token
      else ptr_value_transport births positions (phi_prov s.vs_prev_bb TG h)
        (phi_taint s.vs_prev_bb tn h) sv tv)
    (eval_one_phi s h) (eval_one_phi t h)` by
    (irule ptr_mixed_eval_one_phi >> gvs[] >> metis_tac[]) >>
  gvs[eval_phis_def, AllCaseEqs()] >>
  gvs[optionTheory.OPTREL_def] >> PairCases_on `x0` >> gvs[] >>
  rename1 `eval_one_phi s h = SOME (out,sv)` >>
  `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
  reverse conj_tac
  >- gvs[ptr_core_shared_def, ptr_shared_fields_def, update_var_def] >>
  simp[phis_prov_def, phis_taint_def] >>
  irule ptr_mixed_vars_update >>
  rpt (goal_assum (drule_at Any)) >>
  reverse (rpt conj_tac)
  >- metis_tac[]
  >- (Cases_on `retpc_var f out` >> gvs[] >>
      metis_tac[ptr_mixed_phis_token]) 
  >- (Cases_on `phi_prov t.vs_prev_bb TG h` >>
      gvs[set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
          FLOOKUP_DRESTRICT, op_taint_def] >>
      Cases_on `retpc_var f out` >> gvs[]) >>
  rpt strip_tac >>
  Cases_on `phi_prov t.vs_prev_bb TG h` >>
  simp[set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  qpat_x_assum `ptr_mixed_vars births positions TG tn f g s t` kall_tac >>
  drule_all ptr_mixed_vars_lookup >> simp[op_taint_def]
QED
