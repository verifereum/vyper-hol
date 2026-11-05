Theory makeSsaCurrentSubstitutionSound
Ancestors makeSsaCurrentStaticDemandProbe makeSsaCurrentCleanupRuntime
  makeSsaCurrentPhiBatch makeSsaCurrentCompletedBatch venomWf
  venomExecSemantics venomState finite_map list alist makeSsaCurrentExecutionHistory

Theorem current_static_copy_subst_sound:
  current_cleanup_shape inst /\ step_inst_base inst st = OK post ==>
  ?u. current_static_copy_subst inst x = SOME (CurrentStaticRead u) /\
    eval_operand x post = eval_operand u st
Proof
  simp[current_cleanup_shape_def] >> rpt strip_tac
  >- (gvs[current_cleanup_nop_step] >>
      qexists `x` >> simp[current_static_copy_subst_def]) >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` mp_tac) >>
  Cases_on `lookup_var src st` >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `x` >> simp[current_static_copy_subst_def, eval_operand_def,
    lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `s = dst` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem current_static_phi_subst_sound:
  !phis st post p x.
  EVERY (\inst. inst.inst_opcode = PHI /\ inst_wf inst) phis /\
  st.vs_prev_bb = SOME p /\ eval_phis st phis = OK post ==>
  ?u. current_static_phi_subst p phis x = SOME (CurrentStaticRead u) /\
    eval_operand x post = eval_operand u st
Proof
  Induct >- (rpt gen_tac >> Cases_on `x` >>
    simp[eval_phis_def, current_static_phi_subst_def]) >>
  rpt gen_tac >> simp[EVERY_DEF] >> strip_tac >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  simp[Once eval_phis_def] >>
  Cases_on `eval_one_phi st h` >> simp[] >>
  PairCases_on `x'` >> simp[] >>
  Cases_on `eval_phis st phis` >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `eval_one_phi _ _ = _` mp_tac >>
  simp[eval_one_phi_def, AllCaseEqs()] >> strip_tac >>
  first_x_assum (qspecl_then [`st`, `v`, `p`, `x`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `x` >> gvs[current_static_phi_subst_def, ALOOKUP_def,
    eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `out = s` >> simp[] >> metis_tac[]
QED

Theorem current_static_phi_prefix_subst_sound:
  EVERY inst_wf (TAKE (phi_prefix_length insts) insts) /\
  st.vs_prev_bb = SOME p /\ eval_phis st insts = OK post ==>
  ?u. current_static_phi_subst p (TAKE (phi_prefix_length insts) insts) x =
    SOME (CurrentStaticRead u) /\ eval_operand x post = eval_operand u st
Proof
  strip_tac >> irule current_static_phi_subst_sound >>
  simp[current_eval_phis_take, EVERY_CONJ, current_phi_prefix_every]
QED
