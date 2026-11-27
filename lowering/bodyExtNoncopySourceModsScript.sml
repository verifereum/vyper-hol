(* Source observations preserved at a successful no-copy suffix. *)
Theory bodyExtNoncopySourceMods
Ancestors
  abiEncodeArgsScopes bodySavedTargetSourceMods bodySavedTargetWalkMods
  bodyCallSupport bodyInvSplit vyperCallOutcomeFrame vyperMachineFrame
  vyperStorageBackend vyperInterpreter vyperTypeContract exprLowering list

Theorem suffix_frame_from_walk:
  ~exprs_can_mutate cenv ys /\
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (eval_exprs cx ys) /\
  eval_exprs cx ys (src with gas_obs := obs) = (INL vs,dst) ==>
  dst.scopes = src.scopes /\ dst.immutables = src.immutables /\
  (!tr. get_storage cx dst tr = get_storage cx src tr)
Proof
  strip_tac >>
  conj_tac
  >- (drule_all eval_exprs_no_mutation_scopes >> simp[]) >>
  qpat_x_assum `state_rel_frame _ _`
    (qspec_then `src with gas_obs := obs` mp_tac o
     REWRITE_RULE [state_rel_frame_def]) >>
  simp[machine_frame_def] >> strip_tac >>
  Cases >> simp[get_storage_def]
QED

Triviality suffix_runtime_walk_mods:
  contract_inv mods exps ctx cenv cx /\ ~cx.in_deploy /\
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  EVERY (source_body_call_supported cx) (int_calls_exprs ys) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs ys) /\
  ~exprs_can_mutate cenv ys ==>
  state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
    (eval_exprs cx ys)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule saved_exprs_walk_from_calls_mods >>
  qexistsl [`\k. source_body_call_supported cx k /\
      MEM k (linked_live_functions mods exps)`, `cenv`] >>
  simp[EVERY_MEM] >> reverse conj_tac >- fs[EVERY_MEM] >>
  map_every qx_gen_tac [`ty`, `key`, `actuals`, `fallback`] >>
  PairCases_on `key` >> strip_tac >>
  metis_tac[saved_runtime_call_frame]
QED

Triviality every_suffix_support[local]:
  EVERY (\k. source_body_call_supported cx k) (int_calls_exprs ys) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs ys) ==>
  EVERY (\k. source_body_call_supported cx k /\
    MEM k (linked_live_functions mods exps)) (int_calls_exprs ys)
Proof
  simp[listTheory.EVERY_CONJ]
QED


Theorem ext_noncopy_suffix_frame_mods:
  (!ty key actuals fallback.
    (source_body_call_supported cx key /\
      MEM key (linked_live_functions mods exps)) /\
    ~call_can_mutate cenv (IntCall key) /\
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_exprs cx actuals) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
  ~exprs_can_mutate cenv ys /\
  EVERY (\k. source_body_call_supported cx k) (int_calls_exprs ys) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs ys) /\
  eval_exprs cx ys (src with gas_obs := obs) = (INL vs,dst) ==>
  dst.scopes = src.scopes /\ dst.immutables = src.immutables /\
  (!tr. get_storage cx dst tr = get_storage cx src tr)
Proof
  strip_tac >>
  `state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_exprs cx ys)` by
    (irule saved_exprs_walk_from_calls_mods >>
     qexistsl [`\k. source_body_call_supported cx k /\
       MEM k (linked_live_functions mods exps)`, `cenv`] >>
     BETA_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     irule every_suffix_support >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  match_mp_tac suffix_frame_from_walk >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED
