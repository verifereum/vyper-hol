(* Source frames at a reached nonmutating suffix, using the checked signature domain. *)
Theory bodyExtNoncopySigReachedFrameMods
Ancestors
  bodyExtNoncopySigWalkMods bodySavedReadonlyCalleeMods bodySavedTargetSourceMods
  bodySavedCallMutabilityMods supportedProgram bodyCallSupport bodyInvSplit
  vyperStorageBackend vyperCallOutcomeFrame
  vyperMachineFrame vyperInterpreter vyperTypeContract exprLowering list

Theorem ext_noncopy_reached_sig_suffix_frame_mods:
  contract_inv mods exps ctx cenv cx /\
  check_contract F cx.layouts cx.txn.target mods = SOME runtime_art /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ~exprs_can_mutate cenv ys /\
  EVERY (source_body_call_supported cx) (int_calls_exprs ys) /\
  EVERY (\k. IS_SOME (FLOOKUP art.cta_fn_sigs k)) (int_calls_exprs ys) /\
  eval_exprs cx ys (src with gas_obs := obs) = (INL vs,dst) ==>
  dst.scopes = src.scopes /\ dst.immutables = src.immutables /\
  (!tr. get_storage cx dst tr = get_storage cx src tr) /\
  (!tr slot tv v. read_storage_slot cx tr slot tv src = (INL v,src) ==>
    read_storage_slot cx tr slot tv dst = (INL v,dst))
Proof
  strip_tac >>
  `!ty key actuals fallback.
      (source_body_call_supported cx key /\
       IS_SOME (FLOOKUP art.cta_fn_sigs key)) /\
      ~call_can_mutate cenv (IntCall key) /\
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_exprs cx actuals) ==>
      state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
        (eval_expr cx (Call ty (IntCall key) actuals fallback))` by
    (rpt gen_tac >> strip_tac >> PairCases_on `key` >>
     `?tops. get_module_code cx key0 = SOME tops` by
       fs[source_body_call_supported_def] >>
     `?callable. lookup_callable_function cx.in_deploy key1 tops = SOME callable` by
       (qpat_x_assum `source_body_call_supported cx (key0,key1)` mp_tac >>
        Cases_on `key0` >> simp[source_body_call_supported_def, PULL_EXISTS] >>
        rpt strip_tac >> gvs[] >>
        fs[supported_linked_callee_def, optionTheory.IS_SOME_EXISTS] >>
        rename1 `supported_function_decl _ _ _ = SOME decl` >>
        PairCases_on `decl` >>
        drule_then assume_tac supported_internal_lookup >>
        simp[lookup_callable_function_def]) >>
     PairCases_on `callable` >>
     drule_all_then assume_tac saved_selected_call_mutability_mods >>
     drule_all_then assume_tac saved_readonly_callee_frames_sig_domain_mods >>
     match_mp_tac saved_checked_call_frame_from_callee_mods >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all_then MATCH_ACCEPT_TAC ext_noncopy_sig_suffix_frame_from_calls_mods
QED
