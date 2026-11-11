Theory concretizePtrTaggedSupport
Ancestors concretizePtrSourceOwnership concretizePtrParamSupport
  concretizePtrDeletedGapHistory concretizePtrChronologicalHistory
  concretizePtrOwnershipErasure concretizePtrPrefixLedger ptrDiscipline
  finite_map list

Theorem ptr_owned_current_static[local]:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions ==>
  ptr_params_ok P a.po_fn a.po_params /\
  ptr_static_support P a.po_fn a.po_prov
Proof
  strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  drule_all ptr_frame_current_static >> simp[]
QED

Theorem ptr_source_tagged_var_support:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  FLOOKUP TG v = SOME tag ==>
  v IN fn_pv P a.po_fn
Proof
  strip_tac >> drule_all ptr_owned_current_static >> strip_tac >>
  drule_all ptr_source_ownership_prov_erases >>
  simp[ptr_ledger_erases_def] >> strip_tac >>
  `tag IN FDOM births` by metis_tac[] >>
  `?site. FLOOKUP births tag = SOME site` by metis_tac[FLOOKUP_DEF] >>
  gvs[ptr_static_support_def] >> metis_tac[]
QED

Theorem ptr_source_tagged_param_support:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  k < LENGTH PT /\ EL k PT = SOME tag ==>
  k IN P a.po_fn.fn_name
Proof
  strip_tac >> drule_all ptr_owned_current_static >> strip_tac >>
  drule_all ptr_source_ownership_params_erases >>
  simp[ptr_params_erases_def, EVERY_EL] >> strip_tac >>
  `tag IN FDOM births` by
    (first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  `?site. FLOOKUP births tag = SOME site` by metis_tac[FLOOKUP_DEF] >>
  gvs[ptr_params_ok_def, EL_MAP, ptr_owner_project_def] >> metis_tac[]
QED
