(* Source facts at the actual post-index endpoint.  In particular, the
   index may change storage; no pre-index array contents are framed. *)
Theory bodyFullTargetArraySource
Ancestors
  targetLocalLive exprSimSource targetPlaceSim vyperTypeStatePreservation
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeEnv vyperTypeSystem
  vyperValue vyperInterpreter vyperState

Theorem target_array_source_cases:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  type_place_target env (SubscriptTarget bt e) = SOME vt /\
  expr_sim_inv cenv cx env mid1 /\
  eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv, mid1) /\
  bind (eval_expr cx e) (read_result cx)
    (mid1 with gas_obs := index_gas) = (INL v, mid2) ==>
  expr_sim_inv cenv cx env mid2 /\
  (?i. v = IntV i /\ expr_result_typed env e (Value (IntV i))) /\
  (!id. target_root bt = NameTarget id ==>
    ?path entry live. pv = PlaceR (MemoryPlace id path) /\
      lookup_scopes id mid2.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL live)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (mid1 with gas_obs := index_gas)` by
    fs[target_pre_def, target_indices_pre_def] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval) >> strip_tac >>
  `is_int_type (expr_type e)` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def,
        AllCaseEqs()] >>
  `?i. v = IntV i` by
    (irule int_typed_value_is_IntV >>
     fs[expr_result_typed_def, expr_runtime_typed_def,
        value_result_typed_def, value_runtime_typed_def] >> metis_tac[]) >>
  gvs[] >> rpt strip_tac >>
  `target_pre cenv cx env (SubscriptTarget bt e)
     (es with gas_obs := base_gas)` by fs[target_pre_def] >>
  qpat_x_assum `target_pre _ _ _ _ es` kall_tac >>
  drule_all local_subscript_index_live >> simp[]
QED
