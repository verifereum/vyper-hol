(* Source observations at the reached runtime ABI argument suffix. *)
Theory bodyAbiEncodeSuffixObservationsMods
Ancestors
  bodyExtNoncopySourceMods bodySavedTargetSourceMods bodyCallSupport
  bodyInvSplit vyperStorageBackend vyperCallOutcomeFrame vyperMachineFrame
  vyperTypeContract vyperInterpreter exprLowering list

Theorem abi_encode_runtime_suffix_observations_mods:
  contract_inv mods exps ctx cenv cx /\ ~cx.in_deploy /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  EVERY (source_body_call_supported cx) (int_calls_exprs xs) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs xs) /\
  ~exprs_can_mutate cenv xs /\
  eval_exprs cx xs (mid with gas_obs := obs) = (INL vs,ee with gas_obs := []) ==>
  ee.immutables = mid.immutables /\
  (!tr. get_storage cx ee tr = get_storage cx mid tr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!ty key actuals fallback.
      (source_body_call_supported cx key /\
       MEM key (linked_live_functions mods exps)) /\
      ~call_can_mutate cenv (IntCall key) /\
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_exprs cx actuals) ==>
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_expr cx (Call ty (IntCall key) actuals fallback))` by
    (rpt gen_tac >> strip_tac >> PairCases_on `key` >>
     metis_tac[saved_runtime_call_frame]) >>
  `(ee with gas_obs := []).immutables = mid.immutables /\
   (!tr. get_storage cx (ee with gas_obs := []) tr = get_storage cx mid tr)` by
    (drule_at (Pat `eval_exprs _ _ _ = _`) ext_noncopy_suffix_frame_mods >>
     disch_then (qspecl_then [`mods`,`exps`,`cenv`] mp_tac) >> simp[ETA_AX] >> metis_tac[]) >>
  conj_tac >- fs[] >>
  Cases >> fs[boolTheory.FORALL_BOOL, get_storage_def]
QED
