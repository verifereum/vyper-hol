Theory simplifyCfgSsaform
Ancestors
  simplifyCfgStruct simplifyCfgDefs venomWf pair

(* Round preservation lifts through the fuel bound independently of label maps. *)
Theorem simplify_cfg_iter_with_labels_ssa:
  !n func. ssa_form func /\ wf_function func ==>
    ssa_form (FST (simplify_cfg_iter_with_labels n func))
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >>
  drule_all simplify_cfg_round_ssa >>
  drule simplify_cfg_round_wf >>
  Cases_on `simplify_cfg_round_with_labels func` >>
  simp[simplify_cfg_round_def] >> rpt strip_tac >>
  simp[Once simplify_cfg_iter_with_labels_def] >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[]
QED
