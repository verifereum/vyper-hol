Theory bodyPtrPopTargetSimBoundary
Ancestors
  bodyPtrPopTargetDefs bodyPtrPopTargetFactor bodyPtrPreds
  bodyPtrEnvBuiltinsBoundary targetPlaceSim targetPlaceLive
  exprSimHypsDefs bodySim bodySimAugPlaceLoad typedCopyLayoutPtr
  representationCleanPtr

(* The intermediate state is arbitrary: it is the state at the base cut,
   not necessarily the state at which the whole target started. *)
Theorem target_index_body_sim_ptr:
  body_inv tops ctx cenv cx /\
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_indices_pre cenv cx env (SubscriptTarget bt e) /\
  eval_base_place cx bt s = (INL pv,s1) /\
  expr_sim_inv cenv cx env es ==>
  expr_sim_ptr d ctx PG func cenv cx ty e es
Proof
  rpt strip_tac >>
  drule_all pop_target_index_ptr_premise >> strip_tac >>
  irule body_expr_ptr_sim >>
  gvs[target_indices_pre_def] >> metis_tac[]
QED

Theorem target_attribute_ptr_premises:
  body_base_target_ptr_ok cx (AttributeTarget bt fld) /\
  target_pre cenv cx env (AttributeTarget bt fld) es /\
  (!id. target_root (AttributeTarget bt fld) = NameTarget id ==>
        local_target_live cx id (AttributeTarget bt fld)) /\
  (!src id. target_root (AttributeTarget bt fld) =
             TopLevelNameTarget (src,id) ==>
             EVERY pure_expr (target_indices (AttributeTarget bt fld))) ==>
  body_base_target_ptr_ok cx bt /\ target_pre cenv cx env bt es /\
  (!id. target_root bt = NameTarget id ==> local_target_live cx id bt) /\
  (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
             EVERY pure_expr (target_indices bt))
Proof
  simp[body_base_target_ptr_ok_def, target_pre_def, immutable_root_def, target_root_def,
       target_indices_pre_def, target_indices_def, local_target_live_def]
QED

Theorem target_subscript_ptr_premises:
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (!id. target_root (SubscriptTarget bt e) = NameTarget id ==>
        local_target_live cx id (SubscriptTarget bt e)) /\
  (!src id. target_root (SubscriptTarget bt e) =
             TopLevelNameTarget (src,id) ==>
             EVERY pure_expr (target_indices (SubscriptTarget bt e))) ==>
  body_base_target_ptr_ok cx bt /\ target_pre cenv cx env bt es /\
  (!id. target_root bt = NameTarget id ==> local_target_live cx id bt) /\
  (!src id. target_root bt = TopLevelNameTarget (src,id) ==>
             EVERY pure_expr (target_indices bt))
Proof
  simp[body_base_target_ptr_ok_def, target_pre_def, immutable_root_def, target_root_def,
       target_indices_pre_def, target_indices_def, local_target_live_def,
       listTheory.EVERY_APPEND] >> metis_tac[]
QED

(* Current-value resolution, rather than a historical read_memory_path
   result, is essential here.  The local may have changed during an index. *)
Theorem target_live_dynarray_header_clean:
  value_has_type tv a /\ well_formed_type_value tv /\
  mem_path_offset tv path = SOME (off,ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts tv a path = INL (ArrayV (DynArrayV vs)) /\
  (!m. mem_agree_outside tn.t_mem mem m ==> val_in_memory tv a locbase m) ==>
  !i. locbase + off <= i /\ i < locbase + off + 32 ==> i NOTIN tn.t_mem
Proof
  strip_tac >>
  `!m. mem_agree_outside tn.t_mem mem m ==>
       val_in_memory (ArrayTV etv (Dynamic cap)) (ArrayV (DynArrayV vs))
         (locbase + off) m` by
    (rpt strip_tac >> irule aug_place_path_project >> metis_tac[]) >>
  drule dynarray_in_memory_robust_length >> strip_tac >>
  metis_tac[robust_mem_word_at_clean]
QED
