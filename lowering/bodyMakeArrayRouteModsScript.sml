(* Layout and paired code cuts for homogeneous MakeArray. *)
Theory bodyMakeArrayRouteMods
Ancestors
  bodyMakeElementsContractMods exprBodyPreProps exprBodyPreTypingProps exprSimHypsDefs
  exprSimAggregateLayout exprSimAggregateLoops exprSimAggregateSource
  typedMemoryCopy vyperTypeInvariants vyperTypeEvalCaseProofs vyperTypeSystem
  allocLimits allocLimitsProps gasShadowCompileBase exprLoweringProps fragExec
  list rich_list words

Theorem make_array_source_layout_mods:
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  ?tv. ann = ArrayT et n /\
    evaluate_type (get_tenv cx) et = SOME tv /\
    evaluate_type (get_tenv cx) (ArrayT et n) = SOME (ArrayTV tv n) /\
    EVERY (\e. arg_type_fits (expr_type e) et) args /\
    compatible_bound n (LENGTH args) /\ 0 < type_slot_size tv /\
    type_memory_bytes ce et = type_memory_size tv /\
    type_memory_bytes ce (ArrayT et n) = type_memory_size (ArrayTV tv n) /\
    (if (case n of Dynamic _ => T | _ => F) then 32 else 0) +
      LENGTH args * type_memory_size tv <= type_memory_bytes ce (ArrayT et n) /\
    type_memory_bytes ce (ArrayT et n) < dimword (:256)
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP env_consistent_type_defs_get_tenv) >>
  fs[Once well_typed_expr_def, well_typed_builtin_app_def, EVERY_MAP] >>
  gvs[] >>
  `?tv. evaluate_type (get_tenv cx) et = SOME tv /\ 0 < type_slot_size tv /\
    0 < bound_length n /\ type_slot_size (ArrayTV tv n) < dimword (:256)` by
    (qpat_x_assum `well_formed_type _ (ArrayT _ _)` mp_tac >>
     rewrite_tac[well_formed_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) et` >>
     simp[Once vyperValueTheory.evaluate_type_def]) >>
  rename1 `evaluate_type (get_tenv cx) et = SOME tv` >>
  `!ty rt. evaluate_type (get_tenv cx) ty = SOME rt ==>
     type_memory_bytes ce ty = type_memory_size rt` by
    (rpt strip_tac >> irule typed_copy_memory_size >> qexists `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
  `evaluate_type (get_tenv cx) (ArrayT et n) = SOME (ArrayTV tv n)` by
    simp[Once vyperValueTheory.evaluate_type_def] >>
  `type_memory_bytes ce (ArrayT et n) < dimword (:256)` by
    (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, alloc_limits_expr_def, wordsTheory.dimword_def] >>
     decide_tac) >>
  qpat_assum `!ty rt. _ ==> type_memory_bytes _ ty = _`
    (qspec_then `ArrayT et n` (drule_then assume_tac)) >>
  simp[] >> Cases_on `n` >>
  gvs[vyperValueTheory.compatible_bound_def, valueEncodingTheory.type_memory_size_def] >>
  simp[arithmeticTheory.LE_MULT_RCANCEL]
QED
