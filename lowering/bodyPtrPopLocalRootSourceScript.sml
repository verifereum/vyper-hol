Theory bodyPtrPopLocalRootSource
Ancestors
  exprSimPop vyperInterpreter vyperState vyperValue vyperValueOperation
  vyperLookup vyperTyping vyperTypeSystem finite_map list

Theorem pop_local_source_empty_ptr:
  lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
  entry.value = ArrayV (DynArrayV []) ==>
  eval_expr cx (Pop ann (NameTarget id)) es =
    (INR (Error (RuntimeError "pop empty memory array")), es)
Proof
  strip_tac >>
  drule lookup_scopes_find_containing_scope >> strip_tac >>
  `IS_SOME (lookup_scopes id es.scopes)` by simp[] >>
  simp[Once evaluate_def, bind_def] >>
  drule_then (qspec_then `cx` SUBST1_TAC) eval_target_place_name >>
  simp[pop_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, return_def,
       raise_def, lift_sum_def, read_memory_path_def, evaluate_subscripts_def,
       check_def]
QED

Theorem pop_local_source_nonempty_ptr:
  find_containing_scope id es.scopes = SOME (pre, env, entry, rest) /\
  lookup_scopes id es.scopes = SOME entry /\ entry.assignable /\
  entry.value = ArrayV (DynArrayV vs) /\ vs <> [] ==>
  eval_expr cx (Pop ann (NameTarget id)) es =
    (INL (PlaceR (MemoryPlace id [ValueSubscript (IntV &(LENGTH vs - 1))])),
     es with scopes := pre ++ env |+ (id, pop_name_entry entry vs) :: rest)
Proof
  strip_tac >>
  Cases_on `eval_expr cx (Pop ann (NameTarget id)) es` >>
  drule_all eval_pop_name >> simp[] >> strip_tac >> gvs[]
QED
