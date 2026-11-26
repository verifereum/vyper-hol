(* Recover the compiler's length-word path from the reached memory path. *)
Theory bodyPopReachedMemoryDynarrayMods
Ancestors
  bodyRawLocalBytesLayoutMods tuplePlaceGeometry placeMemoryTypedBase
  exprSimHypsDefs exprSimProps loweringPosts compileEnv vyperValue
  finite_map alist list pair
Libs pairLib

Theorem reached_struct_step_exists[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) t = SOME (StructTV fs) /\
  mem_field_offset fs id = SOME (k,etv) ==>
  ?p. type_step_offset cenv t (AttrSubscript id) = SOME p
Proof
  strip_tac >>
  `?sid. t = StructT sid` by
    (qpat_x_assum `evaluate_type _ t = _` mp_tac >> Cases_on `t` >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  gvs[] >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_mods_def] >>
  drule_all_then strip_assume_tac typed_memory_struct_evaluation >>
  drule_then strip_assume_tac mem_field_offset_sound >>
  `MAP FST fs = MAP FST fields` by
    (qpat_x_assum `MAP FST fields = MAP FST args` kall_tac >>
     qpat_assum `StructTV fs = _` mp_tac >>
     simp[MAP_ZIP]) >>
  `ALOOKUP fields id <> NONE` by metis_tac[alistTheory.ALOOKUP_NONE, optionTheory.NOT_SOME_NONE] >>
  Cases_on `ALOOKUP fields id` >> gvs[] >> PairCases_on `x` >>
  simp[type_step_offset_def, get_struct_fields_def]
QED

Theorem reached_nontuple_step[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  (!ts. tv <> TupleTV ts) /\
  mem_step_offset tv sb = SOME (k,etv) ==>
  ?et. type_step_offset cenv t sb = SOME (k,et) /\
       evaluate_type (get_tenv cx) et = SOME etv
Proof
  strip_tac >>
  `?p. type_step_offset cenv t sb = SOME p` suffices_by
    (strip_tac >> PairCases_on `p` >>
     `type_path_offset cenv t [sb] = SOME (p0,p1)` by simp[type_path_offset_def] >>
     drule_all_then strip_assume_tac type_path_offset_mem_mods >>
     gvs[mem_path_offset_def]) >>
  drule mem_step_offset_shape >> strip_tac >> gvs[]
  >- (drule_all_then ACCEPT_TAC reached_struct_step_exists)
  >- (`?et. t = ArrayT et (Fixed n)` by
        (qpat_x_assum `evaluate_type _ t = _` mp_tac >> Cases_on `t` >>
         simp[evaluate_type_def, AllCaseEqs()]) >>
      gvs[type_step_offset_def]) >>
  `?et. t = ArrayT et (Dynamic n)` by
    (qpat_x_assum `evaluate_type _ t = _` mp_tac >> Cases_on `t` >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  gvs[type_step_offset_def]
QED

Theorem reached_nontuple_path[local]:
  !path t tv k ptv.
    expr_sim_inv_mods mods cenv cx env es /\
    evaluate_type (get_tenv cx) t = SOME tv /\
    tuple_place_no_tuple_step tv path /\
    mem_path_offset tv path = SOME (k,ptv) ==>
    ?pt. type_path_offset cenv t path = SOME (k,pt) /\
         evaluate_type (get_tenv cx) pt = SOME ptv
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[mem_path_offset_def, type_path_offset_def] >>
  gvs[mem_path_offset_def, AllCaseEqs(), EXISTS_PROD, PULL_EXISTS] >>
  drule_then (fn th => gvs[th]) tuple_place_no_tuple_step_cons >>
  drule_all_then strip_assume_tac reached_nontuple_step >>
  first_x_assum drule_all >> strip_tac >> simp[type_path_offset_def]
QED

Theorem pop_reached_memory_dynarray_len_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_var_type id = SOME root_ty /\
  evaluate_type (get_tenv cx) root_ty = SOME root_tv /\
  mutable_place_path root_tv path /\
  mem_path_offset root_tv path = SOME (k,ArrayTV etv (Dynamic n)) ==>
  dynarray_len_untupled cenv id k
Proof
  strip_tac >> drule_all_then assume_tac tuple_place_mutable_path_barrier >>
  drule_all_then strip_assume_tac reached_nontuple_path >>
  `?et. pt = ArrayT et (Dynamic n)` by
    (qpat_x_assum `evaluate_type _ pt = _` mp_tac >> Cases_on `pt` >>
     simp[evaluate_type_def, AllCaseEqs()]) >>
  gvs[dynarray_len_untupled_def] >>
  qexistsl_tac [`path`, `et`, `n`] >> simp[] >> rpt strip_tac >>
  drule_all_then strip_assume_tac type_path_offset_mem_mods >>
  `?ts. ptv = TupleTV ts` by
    (qpat_x_assum `evaluate_type _ (TupleT _) = _` mp_tac >>
     simp[evaluate_type_def, AllCaseEqs(), PULL_EXISTS] >>
     rpt strip_tac >> qexists_tac `tvs` >> simp[]) >>
  qpat_x_assum `tuple_place_no_tuple_step _ _`
    (mp_tac o REWRITE_RULE [tuple_place_no_tuple_step_def]) >>
  disch_then (qspecl_then [`pre`, `sb`, `rest`, `j`, `ts'`] mp_tac) >> gvs[]
QED
