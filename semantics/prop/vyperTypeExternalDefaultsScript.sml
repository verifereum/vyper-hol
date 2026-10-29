Theory vyperTypeExternalDefaults
Ancestors
  list finite_map option pair vyperState
  vyperInterpreter vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeInitialState vyperTypeEvalSoundness
  vyperTypeEnvPreservation vyperEvalPreservesImmutablesDom
  vyperEvalPreservesScopes vyperExprNoControl
  vyperTypeContract vyperTypeContractFunction vyperTypeContractContext
  vyperTypeBindArguments vyperContext vyperTyping vyperTypeSystem
  vyperTypeStmtResult vyperTypeEnvExtension
  vyperTypeCallGraph vyperTypeCallGraphSoundness vyperTypeCallStackSoundness
  alist rich_list

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
  >~ [`find_var_decl_by_name _ _ = SOME (StorageVarDecl _ _,_)`]
  >- metis_tac[]
  >~ [`find_var_decl_by_name _ _ = SOME (HashMapVarDecl _ _ _,_)`]
  >- metis_tac[]
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
  drule (cj 6 eval_preserves_tv) >> strip_tac >>
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
  drule_all (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_mutual))) >>
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
  simp[eval_external_defaults_cons, read_result_def, evaluate_def,
       bind_def, return_def]
QED

(* Fail rather than silently export an admitted prerequisite. *)
val () = List.app (fn (_, th) =>
  if List.null (List.filter (fn s => s <> "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "stateful external-default boundary has oracle dependencies")
  (DB.thms "vyperTypeExternalDefaults");

(* Entry phases expose the actual post-transfer and post-default states.  A
   successful body result (including return) cannot originate in the defaults. *)
Theorem external_entry_send_no_control:
  send_call_value mut cx st = (INR exc,rt) ==> no_control_exc exc
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
  >- (irule transfer_value_no_control >>
      qexistsl [`cx.txn.value`, `cx.txn.sender`, `st`, `rt`, `cx.txn.target`] >>
      simp[]) >>
  simp[no_control_exc_def]
QED

Theorem external_entry_success_phases:
  (do
     send_call_value mut cx;
     dflt_vs <- eval_external_defaults cx es;
     case bind_arguments tenv args (vals ++ dflt_vs) of
       NONE => raise (Error (RuntimeError "call bind_arguments"))
     | SOME env => do set_scopes [env]; action od
   od) st = (res,rt) /\
  (res = INL () \/ ?v. res = INR (ReturnException v)) ==>
  ?s1 dflt_vs s2 env.
    send_call_value mut cx st = (INL (),s1) /\
    eval_external_defaults cx es s1 = (INL dflt_vs,s2) /\
    bind_arguments tenv args (vals ++ dflt_vs) = SOME env /\
    action (s2 with scopes := [env]) = (res,rt)
Proof
  simp[bind_def, ignore_bind_def, set_scopes_def, return_def, raise_def] >>
  Cases_on `send_call_value mut cx st` >> Cases_on `q` >> simp[]
  >- (Cases_on `eval_external_defaults cx es r` >> Cases_on `q` >> simp[]
      >- (rename1 `eval_external_defaults cx es r = (INL dvs,s2)` >>
          Cases_on `bind_arguments tenv args (vals ++ dvs)` >>
          simp[bind_def, set_scopes_def, return_def, raise_def] >>
          rpt strip_tac >> metis_tac[]) >>
      rpt strip_tac >> gvs[] >> drule eval_external_defaults_no_control >>
      simp[no_control_exc_def]) >>
  rpt strip_tac >> gvs[] >> drule external_entry_send_no_control >>
  simp[no_control_exc_def]
QED

Theorem external_call_result_success_cases:
  (\(res,am_out,rqs). (res,am_out,rqs))
  (case body_res of
     (INL (), st) =>
       (case unlock st of
          (INL (), st') => (INL NoneV, abstract_machine_from_state srcs exps layouts st', st'.requests)
        | (INR e, st') => (INR e, am, st'.requests))
   | (INR (ReturnException v_ret), st) =>
       (case unlock st of
          (INL (), st') =>
            (case evaluate_type tenv ret of
               NONE => (INR (Error (TypeError "eval ret")), am, st'.requests)
             | SOME tv =>
                 case safe_cast tv v_ret of
                   NONE => (INR (Error (TypeError "ext cast ret")), am, st'.requests)
                 | SOME v_cast =>
                     (INL v_cast, abstract_machine_from_state srcs exps layouts st', st'.requests))
        | (INR e, st') => (INR e, am, st'.requests))
   | (INR e, st) => (INR e, am, st.requests)) = (INL v, am_out, rqs) ==>
  ?res st_body st_unlocked.
    body_res = (res,st_body) /\
    (res = INL () \/ ?v_ret. res = INR (ReturnException v_ret)) /\
    unlock st_body = (INL (),st_unlocked) /\
    am_out = abstract_machine_from_state srcs exps layouts st_unlocked /\
    rqs = st_unlocked.requests
Proof
  PairCases_on `body_res` >> Cases_on `body_res0` >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >> metis_tac[]
QED

Theorem call_external_function_success_phases:
  call_external_function orc am cx nr mut ts mods args dflts vals body ret =
    (INL v,am_out,rqs) ==>
  ?am_c s1 dflt_vs s2 env res st_body st_unlocked.
    (if cx.in_deploy then evaluate_all_constants cx am cx.txn.target mods
     else SOME am) = SOME am_c /\
    send_call_value mut cx
      (initial_state am_c [FEMPTY] with <|outcomes := orc; requests := []|>) =
      (INL (),s1) /\
    eval_external_defaults cx (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) s1 =
      (INL dflt_vs,s2) /\
    bind_arguments (type_env_all_modules mods) args (vals ++ dflt_vs) = SOME env /\
    (do
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ());
       eval_stmts cx body
     od) (s2 with scopes := [env]) = (res,st_body) /\
    (res = INL () \/ ?v_ret. res = INR (ReturnException v_ret)) /\
    (if nr /\ ~(mut = View \/ mut = Pure) then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) st_body = (INL (),st_unlocked) /\
    am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
    rqs = st_unlocked.requests
Proof
  simp[call_external_function_def] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `if cx.in_deploy then evaluate_all_constants cx am cx.txn.target mods else SOME am` >>
  simp[] >> strip_tac >>
  drule external_call_result_success_cases >> strip_tac >>
  qpat_x_assum `(\(res,am_out,rqs). _) _ = _` kall_tac >>
  drule external_entry_success_phases >> simp[] >> strip_tac >>
  qexistsl [`s1`, `dflt_vs`, `s2`, `env`, `res`, `st_body`, `st_unlocked`] >>
  simp[]
QED

Theorem eval_external_defaults_preserves_tv:
  eval_external_defaults cx es st = (res,rt) ==> preserves_tv cx st rt
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  drule (cj 6 eval_preserves_tv) >>
  simp[preserves_tv_def] >> metis_tac[]
QED

Theorem checked_explicit_external_current_body_sound:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  body_entry_ready art cx scope st /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  eval_stmts cx body st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\
  no_type_error_result res /\
  (!v. res = INR (ReturnException v) ==>
    ?tv. evaluate_type (type_env_all_modules mods) ret = SOME tv /\ value_has_type tv v)
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup_current >> strip_tac >>
  `env_body.type_defs = type_env_all_modules mods` by
    (qpat_x_assum `env_consistent env_body cx st` mp_tac >>
     simp[env_consistent_def, env_context_consistent_def,
          get_tenv_def, initial_evaluation_context_def]) >>
  drule_all (cj 2 eval_scc_type_sound_mutual) >> strip_tac >> simp[] >>
  rpt strip_tac >> gvs[] >>
  gvs[return_exception_typed_def, env_extends_def, value_runtime_typed_def]
QED

Theorem defaults_env_FOLDL_extend_local[local]:
  !args env.
    defaults_env (FOLDL (\env (id,ty). extend_local env id ty T) env args) =
    defaults_env env
Proof
  Induct >> simp[] >> Cases >> simp[extend_local_def, defaults_env_def]
QED

Theorem defaults_env_function_entry_env:
  defaults_env (function_entry_env art mods src args) = artifact_env art mods src
Proof
  simp[function_entry_env_def, defaults_env_FOLDL_extend_local] >>
  simp[defaults_env_def, artifact_env_def]
QED

Theorem checked_external_suffix_call_evaluation_safe:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts ==>
  call_evaluation_safe
    (initial_evaluation_context am.sources am.layouts tx src)
    (int_calls_exprs (DROP k dflts))
Proof
  strip_tac >>
  `calls_follow_call_graph (contract_call_edges mods) (src,tx.function_name)
     (int_calls_exprs dflts)` by
    (rw[calls_follow_call_graph_def, EVERY_MEM, call_edge_rel_def] >>
     irule contract_call_edges_function >>
     qexistsl [`args`, `body`, `dflts`, `mut`, `nr`, `raw`, `ret`, `ts`, `External`] >>
     simp[function_int_calls_def] >> metis_tac[ALOOKUP_MEM]) >>
  `calls_follow_call_graph (contract_call_edges mods) (src,tx.function_name)
     (int_calls_exprs (DROP k dflts))` by
    (irule calls_follow_int_calls_exprs_DROP >> simp[]) >>
  `(initial_evaluation_context am.sources am.layouts tx src) =
   ((initial_evaluation_context am.sources am.layouts tx src) with
      stk := [(src,tx.function_name)])` by
    simp[initial_evaluation_context_def] >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [``:'a`` |-> ``:num``]
    checked_contract_call_evaluation_safe_singleton) >>
  qexistsl [`art`, `am.layouts`, `mods`] >>
  simp[initial_evaluation_context_def]
QED

Theorem checked_external_suffix_static:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  well_typed_exprs (artifact_env art mods src) (DROP k dflts) /\
  call_evaluation_safe cx (int_calls_exprs (DROP k dflts))
Proof
  strip_tac >>
  `External <> Deploy` by simp[] >>
  drule_all check_contract_runtime_function_body_MEM >> strip_tac >>
  conj_tac
  >- (irule well_typed_exprs_DROP >>
      fs[check_function_body_def, defaults_env_function_entry_env]) >>
  gvs[] >> drule_all checked_external_suffix_call_evaluation_safe >> simp[]
QED

Theorem checked_external_empty_frame_ready:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\ state_well_typed st /\
  accounts_well_typed st.accounts /\
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx st.immutables ==>
  env_consistent (artifact_env art mods src) cx (st with scopes := [FEMPTY]) /\
  state_well_typed (st with scopes := [FEMPTY]) /\ functions_well_typed cx
Proof
  strip_tac >> rpt conj_tac
  >- (rw[env_consistent_def]
      >- (gvs[] >> irule check_contract_env_context_consistent_initial_src >> simp[])
      >- simp[env_scopes_consistent_def, artifact_env_def, lookup_scopes_def]
      >- (gvs[env_immutables_consistent_def, immutables_ready_def, artifact_env_def] >>
          metis_tac[]))
  >- gvs[state_well_typed_def, scope_well_typed_def]
  >> gvs[] >> irule check_contract_functions_well_typed_initial >> simp[]
QED

Theorem checked_explicit_external_body_call_evaluation_safe:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts ==>
  call_evaluation_safe
    (initial_evaluation_context am.sources am.layouts tx src)
    (int_calls_stmts body)
Proof
  rpt strip_tac >>
  `calls_follow_call_graph (contract_call_edges mods) (src,tx.function_name)
     (int_calls_stmts body)` by (
    rw[calls_follow_call_graph_def, EVERY_MEM, call_edge_rel_def] >>
    irule contract_call_edges_function >>
    qexistsl [`args`, `body`, `dflts`, `mut`, `nr`, `raw`, `ret`, `ts`,
              `External`] >>
    simp[function_int_calls_def] >>
    metis_tac[ALOOKUP_MEM]) >>
  `(initial_evaluation_context am.sources am.layouts tx src) =
   ((initial_evaluation_context am.sources am.layouts tx src) with
      stk := [(src,tx.function_name)])` by
    simp[initial_evaluation_context_def] >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [``:'a`` |-> ``:num``]
    checked_contract_call_evaluation_safe_singleton) >>
  qexistsl [`art`, `am.layouts`, `mods`] >>
  simp[initial_evaluation_context_def]
QED

Theorem checked_external_declaration_static:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  ALL_DISTINCT (MAP FST args) /\
  (!arg. MEM arg args ==> ?tv. evaluate_type (type_env_all_modules mods) (SND arg) = SOME tv) /\
  MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
  IS_SOME (evaluate_type (type_env_all_modules mods) ret) /\
  (nr ==> IS_SOME cx.nonreentrant_slot) /\
  call_evaluation_safe cx (int_calls_stmts body)
Proof
  strip_tac >>
  `External <> Deploy` by simp[] >>
  drule_all check_contract_runtime_function_body_MEM >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (gvs[] >> drule_all checked_explicit_external_body_call_evaluation_safe >> simp[]) >>
  gvs[check_function_body_def, params_ok_def, EVERY_MEM, FORALL_PROD,
      initial_evaluation_context_def] >>
  rpt strip_tac >> first_x_assum drule >>
  metis_tac[assignable_type_well_formed, well_formed_type_def, IS_SOME_EXISTS]
QED
