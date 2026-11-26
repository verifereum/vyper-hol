(* Source observation at the actual delayed-read cut of qualified Assign. *)
Theory bodyQualifiedPlaceRawReadMods
Ancestors
  bodyAssignQualifiedStageJoinMods bodySavedTargetSourceMods bodySavedTargetWalkMods
  targetPureWalkScopes targetPurePostTransport bodyPtrPopTargetFragTransport
  vyperMachineFrame vyperCallOutcomeFrame vyperInterpreter vyperState list

(* A call-effect supplier is needed only for deployment references. It
   must describe actual-mode evaluation, not just the compile-time
   mutation test or the runtime lookup of the immediate callee. *)
Theorem qualified_place_raw_read_at_target_mods:
  contract_inv mods exps ctx cenv cx /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_target bt) /\
  ~expr_can_mutate cenv (target_to_expr bt) /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z /\
  read_result cx raw mid = (INL v,mid) /\
  (!q ty k actuals fallback.
    cx.in_deploy /\ raw = PlaceR q /\ source_body_call_supported cx k /\
    MEM k (linked_live_functions mods exps) /\ ~call_can_mutate cenv (IntCall k) /\
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_exprs cx actuals) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr cx (Call ty (IntCall k) actuals fallback))) ==>
  read_result cx raw ee = (INL v,ee)
Proof
  strip_tac >>
  qpat_x_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  Cases_on `raw` >> gvs[cj 1 read_result_def,cj 3 read_result_def,return_def,raise_def] >>
  Cases_on `cx.in_deploy`
  >- suspend "deploy" >>
  drule_all_then (ACCEPT_TAC o CONJUNCT1) saved_target_source_update_mods
QED

Resume qualified_place_raw_read_at_target_mods[deploy]:
  `state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
     (eval_base_place cx bt)` by
    (irule saved_target_walk_from_calls_mods >>
     qexistsl_tac [`\k. source_body_call_supported cx k /\
                        MEM k (linked_live_functions mods exps)`, `cenv`] >>
     fs[EVERY_MEM]) >>
  qabbrev_tac `gs = gas_explicit marks u.vs_gas_readings` >>
  `eval_base_place cx bt (mid with gas_obs := gs) = (INL (PlaceR p),ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[eval_target_place_as_bind,bind_def] >>
     Cases_on `eval_base_place cx bt (mid with gas_obs := gs)` >> simp[] >>
     rename1 `eval_base_place _ _ _ = (base_result,base_state)` >>
     reverse (Cases_on `base_result`) >- simp[raise_def] >>
     rename1 `eval_base_place _ _ _ = (INL place_result,base_state)` >>
     Cases_on `place_result` >> simp[get_place_def,return_def,raise_def]) >>
  drule_all_then (assume_tac o SIMP_RULE (srw_ss()) []) target_walk_scopes >>
  qpat_x_assum `state_rel_frame _ (eval_base_place _ _)`
    (qspec_then `mid with gas_obs := gs` mp_tac o
     REWRITE_RULE [state_rel_frame_def]) >>
  simp[machine_frame_def] >> strip_tac >>
  `ee = mid with <|gas_obs := ee.gas_obs; outcomes := ee.outcomes;
      requests := ee.requests; logs := ee.logs; storage_trace := ee.storage_trace|>` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `ee = _` (once_rewrite_tac o single) >>
  fs[GSYM (cj 2 read_result_def),target_saved_read_oracles]
QED

Finalise qualified_place_raw_read_at_target_mods
