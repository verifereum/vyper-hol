(* Source observations of a successful suffix, indexed by checker signatures. *)
Theory bodyExtNoncopySigWalkMods
Ancestors
  bodyExtNoncopySourceMods bodySavedTargetWalkMods bodyCallSupport
  vyperMachineFrame vyperCallOutcomeFrame vyperStorageBackend
  vyperInterpreter vyperTypeContract exprLowering list finite_map

Theorem ext_noncopy_sig_suffix_frame_from_calls_mods:
  (!ty key actuals fallback.
    (source_body_call_supported cx key /\ IS_SOME (FLOOKUP art.cta_fn_sigs key)) /\
    ~call_can_mutate cenv (IntCall key) /\
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_exprs cx actuals) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
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
  `state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
     (eval_exprs cx ys)` by
    (irule saved_exprs_walk_from_calls_mods >>
     qexistsl [`\k. source_body_call_supported cx k /\
                   IS_SOME (FLOOKUP art.cta_fn_sigs k)`, `cenv`] >>
     simp[EVERY_CONJ] >> fs[EVERY_MEM]) >>
  drule_all suffix_frame_from_walk >> strip_tac >> simp[] >>
  rpt gen_tac >> simp[read_storage_slot_eq] >>
  CASE_TAC >> simp[]
QED
