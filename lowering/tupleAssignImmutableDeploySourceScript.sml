(* Source contracts for an already-loaded immutable tuple element. *)
Theory tupleAssignImmutableDeploySource
Ancestors
  immutableAssignCompose tuplePlaceSourceHead tuplePlaceHead
  exprSimPopNestedLocalSource vyperPlaceResultTyping

Theorem tuple_immutable_source_write:
  body_inv tops ctx ce cx /\ cx.in_deploy /\
  supported_immutable_type tops (src,id) = SOME ity /\
  expr_sim_inv ce cx env es /\
  well_typed_target env (TopLevelNameTarget (src,id)) ity /\
  call_evaluation_safe cx (int_calls_target (TopLevelNameTarget (src,id))) /\
  evaluate_type (get_tenv cx) ity = SOME itv /\ value_has_type itv v ==>
  eval_target_place cx (TopLevelNameTarget (src,id)) es =
    (INL (ImmutablePlace src id []),es) /\
  ?ff. write_place cx (ImmutablePlace src id []) v es = (INL (),ff) /\
       expr_sim_inv ce cx env ff
Proof
  strip_tac >>
  `eval_target_place cx (TopLevelNameTarget (src,id)) es =
    (INL (ImmutablePlace src id []),es)` by
    (irule immutableAssignMetadataTheory.immutable_target_place_state >> metis_tac[]) >>
  simp[] >>
  drule_all immutableAssignMetadataTheory.immutable_assign_bare_global >> strip_tac >>
  drule_all immutableDeployAssignSourceFrameTheory.immutable_assign_source_lookup >> strip_tac >>
  drule_all bodyImmutableAugAssignStoreTheory.immutable_augassign_write_source >>
  disch_then (qspec_then `v` assume_tac) >>
  goal_assum (drule_at Any) >>
  irule tuplePlaceSourceTheory.tuple_place_write_inv >>
  goal_assum (drule_at Any) >>
  qexists `itv` >> simp[vyperStoragePlaceProvenanceTheory.storage_place_region_def] >>
  `env_consistent env cx es /\ state_well_typed es /\
   context_well_typed cx /\ accounts_well_typed es.accounts /\
   functions_well_typed cx /\ env.type_defs = get_tenv cx` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >>
     gvs[vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  drule_all eval_target_place_runtime_facts >> strip_tac >>
  fs[vyperPlaceResultTypingTheory.eval_result_typed_place] >> gvs[]
QED

(* Tuple assignability rules out even zero-sized struct elements.  Alignment
   is the existing type_memory_size_slots boundary; no extra size premise is
   needed by the immutable continuation. *)
Theorem tuple_immutable_element_memory_positive:
  assignable_type tenv (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type tenv (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type tenv (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys ==>
  0 < type_memory_size (EL i tvs) /\ 0 < type_memory_size (EL i ltvs)
Proof
  strip_tac >> drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `0 < type_slot_size (EL i tvs)` by metis_tac[] >>
  `0 < type_memory_size (EL i tvs)` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `type_memory_size (EL i ltvs) = 0 <=> type_memory_size (EL i tvs) = 0` by
    (irule placeMemoryTypeInterfacesTheory.type_widens_to_zero_memory_size >>
     metis_tac[]) >>
  decide_tac
QED
