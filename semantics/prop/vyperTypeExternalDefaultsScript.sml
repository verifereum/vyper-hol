Theory vyperTypeExternalDefaults
Ancestors
  list finite_map option pair vyperState
  vyperInterpreter vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeInitialState vyperTypeEvalSoundness
  vyperTypeEnvPreservation vyperEvalPreservesImmutablesDom
  vyperEvalPreservesScopes vyperExprNoControl
  vyperTypeContract vyperTypeContractFunction vyperTypeContractContext
  vyperTypeBindArguments vyperContext vyperTyping vyperTypeSystem

val _ = Parse.hide "body";

(* Transport readiness using lookup domains and stored type tags, not values. *)
Theorem immutables_ready_preserved_by_frame:
  immutables_ready bg vt cx st.immutables /\
  preserves_tv cx st rt /\
  (!src id.
    IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id) =
    IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP rt.immutables cx.txn.target of SOME m => m | NONE => [])) id)) ==>
  immutables_ready bg vt cx rt.immutables
Proof
  rw[immutables_ready_def]
  >- metis_tac[]
  >> TRY (metis_tac[] >> NO_TAC)
  >> `IS_SOME (FLOOKUP (get_source_immutables src
        (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id)` by
       metis_tac[IS_SOME_EXISTS]
  >> pop_assum (strip_assume_tac o REWRITE_RULE [IS_SOME_EXISTS])
  >> rename1 `FLOOKUP _ id = SOME x`
  >> PairCases_on `x`
  >> drule_all preserves_tv_immutables_type_preserved
  >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem eval_exprs_immutable_lookup_domain:
  eval_exprs cx es st = (res,rt) ==>
  !src id.
    IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id) =
    IS_SOME (FLOOKUP (get_source_immutables src
      (case ALOOKUP rt.immutables cx.txn.target of SOME m => m | NONE => [])) id)
Proof
  strip_tac >>
  drule eval_exprs_preserves_immutables_addr_dom >>
  disch_then (qspec_then `cx.txn.target` mp_tac) >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  Cases_on `ALOOKUP rt.immutables cx.txn.target` >>
  simp[get_source_immutables_def] >> strip_tac >>
  drule_all eval_exprs_preserves_immutables_dom >>
  simp[get_source_immutables_def]
QED

Theorem eval_external_defaults_immutables_ready:
  immutables_ready bg vt cx st.immutables /\
  eval_external_defaults cx es st = (res,rt) ==>
  immutables_ready bg vt cx rt.immutables
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  `immutables_ready bg vt cx r.immutables` suffices_by simp[] >>
  drule (cj 9 eval_preserves_tv) >> strip_tac >>
  drule eval_exprs_immutable_lookup_domain >> strip_tac >>
  irule immutables_ready_preserved_by_frame >>
  qexists `st with scopes := [FEMPTY]` >> simp[]
QED

Theorem eval_external_defaults_no_control:
  eval_external_defaults cx es st = (INR exc,rt) ==> no_control_exc exc
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  drule (cj 2 eval_expr_no_control) >> simp[]
QED

Theorem eval_external_defaults_type_sound:
  well_typed_exprs env es /\
  env_consistent env cx (st with scopes := [FEMPTY]) /\
  state_well_typed st /\
  state_well_typed (st with scopes := [FEMPTY]) /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  eval_external_defaults cx es st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\
  no_type_error_result res /\
  (case res of INL vs => exprs_runtime_typed env es vs | INR exc => no_control_exc exc)
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  `accounts_well_typed (st with scopes := [FEMPTY]).accounts` by simp[] >>
  drule_all (cj 9 eval_all_type_sound_mutual) >>
  strip_tac >>
  Cases_on `q` >> gvs[state_well_typed_def] >>
  drule (cj 2 eval_expr_no_control) >> simp[]
QED

Definition body_entry_ready_def:
  body_entry_ready art cx scope st <=>
    st.scopes = [scope] /\ state_well_typed st /\
    accounts_well_typed st.accounts /\
    immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables
End

(* The current-state setup deliberately does not identify immutable values with
   their values in the incoming machine. *)
Theorem checked_explicit_external_body_setup_current:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  body_entry_ready art cx scope st ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    env_consistent env_body cx st /\ context_well_typed cx /\
    functions_well_typed cx /\ state_well_typed st /\
    accounts_well_typed st.accounts
Proof
  strip_tac >> gvs[body_entry_ready_def] >>
  `functions_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  `External <> Deploy` by simp[] >>
  drule_all checked_function_body_typing_package >> strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >> simp[])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >> gvs[env_immutables_consistent_def] >> rw[] >>
  qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
  simp[immutables_ready_def] >> strip_tac >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`id_str`, `tv`, `v`] mp_tac) >> simp[]
QED

Theorem body_entry_ready_nil_defaults:
  body_entry_ready art cx scope st ==>
  eval_external_defaults cx [] st = (INL [],st) /\
  body_entry_ready art cx scope st
Proof
  simp[]
QED

(* In particular an internal-call default may change accounts.  Its effects
   are retained, while only the caller's local scopes are restored. *)
Theorem external_default_internal_call_effects:
  eval_expr cx (Call ty (IntCall fn) args NONE)
      (st with scopes := [FEMPTY]) = (INL (Value v), changed) ==>
  eval_external_defaults cx [Call ty (IntCall fn) args NONE] st =
      (INL [v], changed with scopes := st.scopes) /\
  (SND (eval_external_defaults cx [Call ty (IntCall fn) args NONE] st)).accounts =
      changed.accounts
Proof
  strip_tac >>
  simp[eval_external_defaults_cons, materialise_def, evaluate_def,
       bind_def, return_def]
QED

(* Fail rather than silently export an admitted prerequisite. *)
val () = List.app (fn (_, th) =>
  if List.null (List.filter (fn s => s <> "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "stateful external-default boundary has oracle dependencies")
  (DB.thms "vyperTypeExternalDefaults");
