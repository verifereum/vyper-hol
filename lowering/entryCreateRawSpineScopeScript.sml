(* Interpret the retained administrative spine without changing its endpoints. *)
Theory entryCreateRawSpineScope
Ancestors
  rawCreateAdminSpine entryCreatePathScope createSizePrefixReplay
  createMarkedPath fragGasOrigin relation list

Theorem admin_ok_spine_prefix:
  admin_ok_spine a b E ctx f s t ==>
  create_expr_prefix a b E ctx f s [] t
Proof
  qid_spec_tac `t` >> qid_spec_tac `s` >>
  rewrite_tac[admin_ok_spine_def] >> ho_match_mp_tac RTC_INDUCT >>
  simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `gas_origin_edge T E ctx f s [] (OK u)` >>
  `gas_origin_edge F E ctx f s [] (OK u)` by
    (drule gas_origin_edge_erase >> simp[] >>
     metis_tac[gas_path_edge_zero_origin]) >>
  `create_expr_prefix a b E ctx f s [] u` by
    (simp[create_expr_prefix_marked] >> irule RTC_SINGLE >>
     simp[create_marked_edge_def,create_prefix_step_def] >> metis_tac[]) >>
  metis_tac[create_expr_prefix_append,APPEND]
QED
