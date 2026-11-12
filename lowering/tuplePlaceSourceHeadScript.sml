(* Source typing at the actual pointer and write endpoints. *)
Theory tuplePlaceSourceHead
Ancestors
  tuplePlaceSource exprSimPopNestedLocalSource vyperStoragePlaceProvenance
  vyperTypeArgFits targetPlaceSimCasesBase targetPlaceSim exprSimHypsDefs
  vyperPlaceResultTyping vyperTargetPlaceWrite vyperTypeInvariants

Theorem tuple_place_destination_value_typed:
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\ value_has_type (EL i ltvs) v ==>
  value_has_type (EL i tvs) v
Proof
  strip_tac >> drule_all tuple_place_type_facts >> strip_tac >>
  metis_tac[type_widens_to_value_has_type, optionTheory.SOME_11]
QED

Theorem tuple_place_target_base_inversion:
  eval_target_place cx bt es = (INL p,ee) ==>
  eval_base_place cx bt es = (INL (PlaceR p),ee)
Proof
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_place_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  strip_tac >> Cases_on `pv` >>
  gvs[vyperStateTheory.get_place_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

Theorem tuple_place_source_target_endpoint:
  target_pre cenv cx env bt es /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_target_place cx bt es = (INL p,ee) ==>
  expr_sim_inv cenv cx env ee /\ runtime_place_typed cx ee p tv /\
  runtime_place_writable cx ee p /\ storage_place_region cx p
Proof
  strip_tac >>
  drule tuple_place_target_base_inversion >> strip_tac >>
  drule_all eval_base_place_sim_inv >> strip_tac >>
  `env_consistent env cx es /\ state_well_typed es /\
   context_well_typed cx /\ accounts_well_typed es.accounts /\
   functions_well_typed cx /\ env.type_defs = get_tenv cx` by
    (fs[target_pre_def, expr_sim_inv_def] >>
     gvs[vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  drule_all eval_target_place_runtime_facts >> strip_tac >>
  drule_all eval_target_place_writable >> strip_tac >>
  drule_all eval_base_place_region >>
  fs[vyperPlaceResultTypingTheory.eval_result_typed_place,
     vyperTargetPlaceWriteTheory.writable_place_result_def,
     storage_result_region_def] >> gvs[]
QED

Theorem tuple_place_source_write_endpoint:
  target_pre cenv cx env bt es /\ well_typed_target env bt ty /\
  call_evaluation_safe cx (int_calls_target bt) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  eval_target_place cx bt es = (INL p,ee) /\
  write_place cx p v ee = (res,ff) ==>
  expr_sim_inv cenv cx env ff
Proof
  strip_tac >> drule_all tuple_place_source_target_endpoint >> strip_tac >>
  drule_all tuple_place_write_inv >> simp[]
QED
