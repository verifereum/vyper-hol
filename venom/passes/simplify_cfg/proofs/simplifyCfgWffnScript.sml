Theory simplifyCfgWffn
Ancestors
  simplifyCfgStruct simplifyCfgDefs venomWf

(* The label evidence is immaterial to structural well-formedness. *)
Theorem simplify_cfg_iter_with_labels_wf:
  !n func. wf_function func ==>
    wf_function (FST (simplify_cfg_iter_with_labels n func))
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def] >>
  rpt strip_tac >>
  drule simplify_cfg_round_wf >>
  simp[simplify_cfg_round_def] >> strip_tac >>
  Cases_on `simplify_cfg_round_with_labels func` >>
  gvs[] >>
  simp[Once simplify_cfg_iter_with_labels_def] >>
  IF_CASES_TAC >- simp[] >>
  first_x_assum (qspec_then `q` mp_tac) >> simp[] >>
  Cases_on `simplify_cfg_iter_with_labels n q` >> gvs[]
QED
