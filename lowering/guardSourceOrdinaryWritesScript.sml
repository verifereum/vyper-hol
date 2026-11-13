(* Ordinary write branches of the selected-prefix evaluator schema. *)
Theory guardSourceOrdinaryWrites
Ancestors
  guardSourceOrdinarySchema vyperInterpreter vyperState vyperStorageFootprint
  vyperTypeEvalSoundness vyperTypeCallGraph vyperTypeSystem
Libs
  guardSourceSchemaLib

Theorem finite_prefix_TupleStores_nil_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_nil_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, return_def, valid_horizon_def]
QED

Theorem finite_prefix_TupleStores_cons_nil:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_cons_nil")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_TupleStores_nil_cons:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStores_nil_cons")
Proof
  rpt strip_tac >> gvs[Once evaluate_def, raise_def, valid_horizon_def]
QED

Theorem finite_prefix_TupleStore_TupleTarget:
  ^(guardSourceSchemaLib.branch finite_prefix_evaluate_ind "TupleStore_TupleTarget")
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[well_typed_atarget_def, int_calls_atarget_def] >>
  qpat_x_assum `ty = TupleT tys` SUBST_ALL_TAC >>
  drule value_runtime_typed_tuple_components >> strip_tac >>
  qpat_x_assum `v = ArrayV (TupleV _)` SUBST_ALL_TAC >>
  qpat_x_assum `!vs. _` (qspec_then `vs` mp_tac) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  qpat_x_assum `!initial_st selected env st res st0. _`
    (qspecl_then [`initial_st`, `selected`] mp_tac) >>
  disch_then irule >> metis_tac[]
QED
