Theory vyperExprNoControl

Ancestors
  pair vyperCreate vyperCreateFrame vyperInterpreter vyperAST vyperMisc
  vyperCallFrame vyperCallOutcome vyperCallOutcomeProps
  vyperCallOutcomeBranches vyperCallOutcomeFrame
  vyperRuntimeAccounts vyperState
Libs
  pairLib monadsyntax evalWalkLib

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);
val _ = hide "body";
val _ = overload_on ("bind", ``vyperState$bind``);
val _ = overload_on ("return", ``vyperState$return``);
val _ = overload_on ("ignore_bind", ``vyperState$ignore_bind``);
val _ = overload_on ("raise", ``vyperState$raise``);
val _ = overload_on ("try", ``vyperState$try``);
val _ = overload_on ("finally", ``vyperState$finally``);

(* ===== Helper predicate ===== *)
Definition no_control_exc_def:
  no_control_exc exc ⇔ (∃str. exc = Error str) ∨ (∃str. exc = AssertException str)
End

Theorem no_control_exc_Error:
  no_control_exc (Error e)
Proof
  simp[no_control_exc_def]
QED

(* ===== Monadic propagation lemmas ===== *)

Theorem bind_INR:
  ∀f g s exc s'.
  bind f g s = (INR exc, s') ⇒
  (f s = (INR exc, s') ∨
   ∃v s''. f s = (INL v, s'') ∧ g v s'' = (INR exc, s'))
Proof
  rpt gen_tac >> strip_tac >> fs[bind_def]
  >> pop_assum mp_tac >> CASE_TAC >> CASE_TAC
QED

Theorem bind_no_control:
  ∀f g s exc s'.
  bind f g s = (INR exc, s') ⇒
  (∀exc' s''. f s = (INR exc', s'') ⇒ no_control_exc exc') ⇒
  (∀v s'' exc' s'''. f s = (INL v, s'') ⇒ g v s'' = (INR exc', s''') ⇒ no_control_exc exc') ⇒
  no_control_exc exc
Proof
  rpt gen_tac >> simp[bind_def, prod_CASE_rator, sum_CASE_rator]
  >> strip_tac >> rpt disch_tac >> gvs[AllCaseEqs()]
QED

Theorem ignore_bind_INR:
  ∀f g s exc s'.
  ignore_bind f g s = (INR exc, s') ⇒
  (f s = (INR exc, s') ∨
   ∃v s''. f s = (INL v, s'') ∧ g s'' = (INR exc, s'))
Proof
  rpt gen_tac >> strip_tac >> fs[ignore_bind_def, bind_def]
  >> pop_assum mp_tac >> CASE_TAC >> CASE_TAC
QED

Theorem handle_function_no_control:
  ∀e s exc s'.
  handle_function e s = (INR exc, s') ⇒ no_control_exc exc
Proof
  Cases >> simp[handle_function_def, return_def, raise_def, no_control_exc_def]
QED

Theorem try_handle_function_no_control:
  ∀f s exc s'.
  try f handle_function s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[try_def, prod_CASE_rator, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs()]
  >> imp_res_tac handle_function_no_control
QED

Theorem finally_no_control:
  ∀f g s exc s'.
  finally f g s = (INR exc, s') ⇒
  (∀exc0 s0. f s = (INR exc0, s0) ⇒ no_control_exc exc0) ⇒
  (∀s0 exc0 s0'. g s0 = (INR exc0, s0') ⇒ no_control_exc exc0) ⇒
  no_control_exc exc
Proof
  rpt gen_tac >> simp[finally_def, ignore_bind_def, bind_def,
    prod_CASE_rator, sum_CASE_rator, raise_def]
  >> strip_tac >> rpt disch_tac
  >> gvs[AllCaseEqs(), raise_def, return_def] >> res_tac
QED

(* ===== Evaluator walk =====
   A goal  M s = (INR exc,s') ==> no_control_exc exc  is reduced through
   M's combinators by bind_no_control and finally_no_control, and closed by a
   primitive's no_control lemma or an induction hypothesis. *)

Theorem no_control_prims:
  (return v s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (raise (Error e) s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (get_scopes s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (set_scopes sc s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (get_accounts s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (update_accounts f s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (get_transient_storage s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (update_transient g s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (get_storage_backend cx tr s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (set_storage_backend cx tr sb s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (set_address_immutables cx imms s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (push_function sf env cx s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (pop_function prev s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (check_not_static cx s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (release_nonreentrant_lock a n s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (adopt_call_outcome rq oc s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (take_call_outcome t cd vo s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (eval_create cx k hs rof tys vs bs s = (INR exc,s') ⇒ no_control_exc exc) ∧
  (check_create_blueprint hs vs s = (INR exc,s') ⇒ no_control_exc exc)
Proof
  Cases_on `tr` >>
  rw[return_def, raise_def, get_scopes_def, set_scopes_def, get_accounts_def,
     update_accounts_def, get_transient_storage_def, update_transient_def,
     get_storage_backend_def, set_storage_backend_def,
     set_address_immutables_def, push_function_def, pop_function_def,
     release_nonreentrant_lock_def, bind_def, adopt_call_outcome_def, UNCURRY,
     no_control_exc_def] >>
  imp_res_tac take_call_outcome_error >>
  imp_res_tac eval_create_exception_is_error >>
  imp_res_tac check_create_blueprint_exception_is_error >> gvs[]
QED

fun is_nc tm = is_comb tm andalso same_const (rator tm) ``no_control_exc``;

(* A rule  INR-result ==> premises ==> no_control_exc exc, restated as
   premises ==> (INR-result ==> no_control_exc exc) for MATCH_MP_TAC. *)
fun nc_rule th =
  let val th = SPEC_ALL th
      val (r, hs) = case fst (strip_imp (concl th)) of r::hs => (r, hs)
                                                   | [] => raise Empty
      val c = list_mk_conj hs
  in DISCH c (DISCH r (List.foldl (uncurry PROVE_HYP) (UNDISCH_ALL th)
       (CONJUNCTS (ASSUME c)))) end;

(* The leaves are no_control_prims and every theorem of this theory so far
   that concludes  M s = (INR exc,s') ==> no_control_exc exc. *)
fun nc_net () =
  let fun is_leaf th = is_imp (concl th) andalso is_nc (snd (dest_imp (concl th)))
  in evalWalkLib.walk_net (map nc_rule [bind_no_control, finally_no_control])
       (map (fn th => (concl th, MATCH_ACCEPT_TAC th))
         (List.filter is_leaf (List.concat (map (map SPEC_ALL o CONJUNCTS o SPEC_ALL)
            (no_control_prims :: map snd (DB.thms "-")))))) end;

val NC_IH_TAC = evalWalkLib.IH_TAC
  {stop = fn tm => is_nc (snd (dest_imp tm)), normalise = I};

(* Introduce quantifiers and guards, but keep the INR result in the goal. *)
fun NC_INTRO (g as (_,w)) =
  (if is_forall w then gen_tac
   else if is_imp w andalso not (is_nc (snd (dest_imp w))) then strip_tac
   else NO_TAC) g;

(* Walk the goal, unfolding the definitions in unfolds at its head.  The net
   is built here so that it holds the lemmas proved so far. *)
fun NC_WALK unfolds g =
  rpt (evalWalkLib.STEP {net = nc_net (), at = LAND_CONV o LHS_CONV,
    unfolds = ignore_bind_def :: unfolds, intros = [NC_INTRO, conj_tac],
    fallbacks = [NC_IH_TAC, evalWalkLib.NORMALISE_IH_TAC NC_IH_TAC]}) g;

fun NC_DEF unfolds = rpt NC_INTRO >> NC_WALK unfolds;

(* ===== Helper function exception lemmas ===== *)

Theorem check_no_control:
  ∀b str s exc s'.
  check b str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[check_def, assert_def, no_control_exc_def]
QED

Theorem type_check_no_control:
  ∀b str s exc s'.
  type_check b str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[type_check_def, assert_def, no_control_exc_def]
QED

Theorem lift_option_no_control:
  ∀x str s exc s'.
  lift_option x str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_option_def, option_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem lift_option_type_no_control:
  ∀x str s exc s'.
  lift_option_type x str s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_option_type_def, option_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem lift_sum_no_control:
  ∀x s exc s'.
  lift_sum x s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_sum_def, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem lift_sum_runtime_no_control:
  ∀x s exc s'.
  lift_sum_runtime x s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt gen_tac >> simp[lift_sum_runtime_def, sum_CASE_rator]
  >> strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem read_storage_slot_no_control:
  ∀cx is_t slot tv s exc s'.
  read_storage_slot cx is_t slot tv s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [read_storage_slot_def]
QED

Theorem return_not_INR[simp]:
  return v s ≠ (INR exc, s')
Proof
  simp[return_def]
QED

Theorem raise_no_control:
  ∀exc s exc' s'.
  raise exc s = (INR exc', s') ⇒ exc' = exc
Proof
  simp[raise_def]
QED

(* ===== Additional helpers for common patterns ===== *)

Theorem transfer_value_no_control:
  ∀from to amt s exc s'.
  transfer_value from to amt s = (INR exc, s') ⇒ no_control_exc exc
Proof
  rpt strip_tac >> drule concrete_send_error >> rw[no_control_exc_def]
QED

Theorem get_immutables_no_control:
  ∀cx src s exc s'.
  get_immutables cx src s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [get_immutables_def, get_address_immutables_def]
QED

Theorem lookup_global_no_control:
  ∀cx src n s exc s'.
  lookup_global cx src n s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [lookup_global_def]
QED

Theorem lookup_flag_mem_no_control:
  ∀cx nsid mid s exc s'.
  lookup_flag_mem cx nsid mid s = (INR exc, s') ⇒ no_control_exc exc
Proof
  Cases_on `nsid` >> NC_DEF [lookup_flag_mem_def]
QED

Theorem acquire_nonreentrant_lock_no_control:
  ∀addr slot is_v s exc s'.
  acquire_nonreentrant_lock addr slot is_v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [acquire_nonreentrant_lock_def]
QED

Theorem push_log_no_control:
  ∀log s exc s'.
  push_log log s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[push_log_def, return_def]
QED

Theorem append_logs_no_control:
  ∀logs s exc s'.
  append_logs logs s = (INR exc, s') ⇒ no_control_exc exc
Proof
  simp[append_logs_def, return_def]
QED

Theorem write_storage_slot_no_control:
  ∀cx is_t slot tv v s exc s'.
  write_storage_slot cx is_t slot tv v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [write_storage_slot_def]
QED

Theorem set_global_no_control:
  ∀cx src n v s exc s'.
  set_global cx src n v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [set_global_def]
QED

Theorem set_immutable_no_control:
  ∀cx src n tv v s exc s'.
  set_immutable cx src n tv v s = (INR exc, s') ⇒ no_control_exc exc
Proof
  NC_DEF [set_immutable_def, get_address_immutables_def]
QED

Theorem resolve_array_element_no_control:
  ∀cx is_t slot tv subs s exc s'.
  resolve_array_element cx is_t slot tv subs s = (INR exc, s') ⇒
  no_control_exc exc
Proof
  ho_match_mp_tac resolve_array_element_ind >> rpt conj_tac >>
  rpt NC_INTRO >> simp_tac bool_ss [Once resolve_array_element_def] >> NC_WALK []
QED

Theorem read_place_no_control:
  read_place cx p st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `p` >> NC_DEF [read_place_def]
QED

Theorem read_result_no_control:
  read_result cx pv st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> NC_DEF [read_result_def]
QED

Theorem read_results_no_control:
  !results cx st exc st'.
    read_results cx results st = (INR exc,st') ==> no_control_exc exc
Proof
  Induct >> NC_DEF [read_results_def]
QED

Theorem switch_BoolV_no_control:
  ∀v f g s exc s'.
  switch_BoolV cx v f g s = (INR exc, s') ⇒
  (∀exc' s''. f s = (INR exc', s'') ⇒ no_control_exc exc') ⇒
  (∀exc' s''. g s = (INR exc', s'') ⇒ no_control_exc exc') ⇒
  no_control_exc exc
Proof
  rpt gen_tac >> rewrite_tac[switch_BoolV_def] >> strip_tac >> rpt disch_tac >>
  drule bind_no_control >> disch_then irule >>
  conj_tac >- metis_tac[read_result_no_control] >>
  rpt strip_tac >> drule read_result_state >> strip_tac >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def, no_control_exc_def] >> metis_tac[]
QED

Theorem result_array_length_no_control:
  ∀cx tv s exc s'.
  result_array_length cx tv s = (INR exc, s') ⇒ no_control_exc exc
Proof
  ho_match_mp_tac result_array_length_ind >> rpt conj_tac >>
  NC_DEF [result_array_length_def]
QED

Theorem place_type_value_no_control:
  place_type_value cx p st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `p` >> NC_DEF [place_type_value_def]
QED

Theorem write_place_no_control:
  write_place cx p v st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `p` >> NC_DEF [write_place_def]
QED

Theorem extend_storage_place_no_control:
  extend_storage_place cx tr slot tv sb st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp[extend_storage_place_def, bind_def, return_def, raise_def,
    no_control_exc_def, AllCaseEqs()] >>
  TRY (rename1 `ValueSubscript v` >> Cases_on `v` >>
    gvs[extend_storage_place_def, bind_def, return_def, raise_def,
      ignore_bind_def, check_def, assert_def, lift_option_type_def,
      vyperMiscTheory.option_CASE_rator,
      no_control_exc_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[return_def]) >>
  metis_tac[lift_option_type_no_control, resolve_array_element_no_control,
    no_control_exc_def]
QED

Theorem extend_place_no_control:
  extend_place cx pv sb st = (INR exc,st') ==> no_control_exc exc
Proof
  map_every qid_spec_tac [`st'`, `exc`, `st`, `sb`, `pv`, `cx`] >>
  ho_match_mp_tac extend_place_ind >> rpt conj_tac >> NC_DEF [extend_place_def]
QED

Theorem get_place_no_control:
  get_place pv st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def, no_control_exc_def]
QED

Theorem select_result_no_control:
  select_result cx ty pv sb st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> NC_DEF [select_result_def]
QED

Theorem conditional_result_no_control:
  conditional_result cx pv st = (INR exc,st') ==> no_control_exc exc
Proof
  Cases_on `pv` >> NC_DEF [conditional_result_def]
QED

Theorem append_place_no_control:
  append_place cx p v st = (INR exc,st') ==> no_control_exc exc
Proof
  map_every qid_spec_tac [`st'`, `exc`, `st`, `v`, `p`, `cx`] >>
  ho_match_mp_tac append_place_ind >> rpt conj_tac >> NC_DEF [append_place_def]
QED

Theorem pop_place_no_control:
  pop_place cx p st = (INR exc,st') ==> no_control_exc exc
Proof
  map_every qid_spec_tac [`st'`, `exc`, `st`, `p`, `cx`] >>
  ho_match_mp_tac pop_place_ind >> rpt conj_tac >> NC_DEF [pop_place_def]
QED

Theorem next_gas_reading_no_control:
  next_gas_reading s = (INR exc, s') ==> no_control_exc exc
Proof
  simp[next_gas_reading_def] >> Cases_on `s.gas_obs` >>
  rw[return_def, raise_def, no_control_exc_def]
QED

Theorem precompile_call_success_no_control:
  precompile_call_success bt s = (INR exc, s') ==> no_control_exc exc
Proof
  strip_tac >> drule vyperStatePreservationTheory.precompile_call_success_exception >>
  rw[] >> simp[no_control_exc_def]
QED

Theorem eval_ext_call_no_control:
  eval_ext_call cx static skip_check sig opts vs st = (INR exc, st') ==>
  no_control_exc exc
Proof
  PairCases_on `sig` >> Cases_on `vs` >>
  NC_DEF [eval_ext_call_def, frame_call_value_def, eval_ext_call_effects_def]
QED

Theorem eval_send_no_control:
  eval_send cx has_gas vs st = (INR exc, st') ==> no_control_exc exc
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def, no_control_exc_def] >>
  Cases_on `t` >> NC_DEF [eval_send_def, frame_call_value_def]
QED

Theorem eval_raw_call_no_control:
  eval_raw_call cx flags target_addr calldata amount gas st = (INR exc, st') ==>
  no_control_exc exc
Proof
  NC_DEF [eval_raw_call_def, frame_call_value_def]
QED

(* ===== Main theorem ===== *)

val NC_EVAL_CASE =
  rpt NC_INTRO >>
  simp_tac bool_ss [Once evaluate_def, lock_if_nr_def, unlock_if_nr_def] >>
  NC_WALK [switch_BoolV_def];

val canonical_no_control_ind = evaluate_ind
  |> Q.SPECL [`\cx s. T`, `\cx ss. T`, `\cx it. T`,
              `\cx ty nm body vs. T`,
              `\cx e. !s exc st'. eval_expr cx e s = (INR exc,st') ==> no_control_exc exc`,
              `\cx es. !s exc st'. eval_exprs cx es s = (INR exc,st') ==> no_control_exc exc`,
              `\cx t. !s exc st'. eval_base_place cx t s = (INR exc,st') ==> no_control_exc exc`,
              `\cx t. !s exc st'. eval_target_place cx t s = (INR exc,st') ==> no_control_exc exc`,
              `\cx g v. T`, `\cx gs vs. T`,
              `\cx es. !s exc st'. eval_expr_results cx es s = (INR exc,st') ==> no_control_exc exc`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV)
  |> PURE_REWRITE_RULE [FORALL_SIMP, AND_CLAUSES, IMP_CLAUSES];

Theorem canonical_eval_no_control_with_results:
  (!cx e s exc st'. eval_expr cx e s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx es s exc st'. eval_exprs cx es s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx t s exc st'. eval_base_place cx t s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx t s exc st'. eval_target_place cx t s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx es s exc st'. eval_expr_results cx es s = (INR exc,st') ==> no_control_exc exc)
Proof
  ho_match_mp_tac canonical_no_control_ind >> rpt conj_tac
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >- NC_EVAL_CASE
  >> NC_EVAL_CASE
QED
Theorem canonical_eval_no_control:
  (!cx e s exc st'. eval_expr cx e s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx es s exc st'. eval_exprs cx es s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx t s exc st'. eval_base_place cx t s = (INR exc,st') ==> no_control_exc exc) /\
  (!cx t s exc st'. eval_target_place cx t s = (INR exc,st') ==> no_control_exc exc)
Proof
  metis_tac[canonical_eval_no_control_with_results]
QED

Theorem eval_expr_results_no_control:
  eval_expr_results cx es st = (INR exc,st') ==> no_control_exc exc
Proof
  metis_tac[canonical_eval_no_control_with_results]
QED

Theorem eval_expr_no_control:
  (∀cx e s exc st'.
    eval_expr cx e s = (INR exc, st') ⇒
    no_control_exc exc) ∧
  (∀cx es s exc st'.
    eval_exprs cx es s = (INR exc, st') ⇒
    no_control_exc exc)
Proof
  metis_tac[canonical_eval_no_control]
QED

Theorem eval_base_place_no_control:
  !t cx st exc st'. eval_base_place cx t st = (INR exc,st') ==> no_control_exc exc
Proof
  metis_tac[canonical_eval_no_control]
QED

Theorem eval_target_place_no_control:
  eval_target_place cx t st = (INR exc,st') ==> no_control_exc exc
Proof
  metis_tac[canonical_eval_no_control]
QED

val tuple_no_control_ind = evaluate_ind
  |> Q.SPECL [`\cx s. T`, `\cx ss. T`, `\cx it. T`,
              `\cx ty nm body vs. T`, `\cx e. T`, `\cx es. T`,
              `\cx t. T`, `\cx t. T`,
              `\cx g v. !st exc st'. assign_tuple_targets cx g v st = (INR exc,st') ==> no_control_exc exc`,
              `\cx gs vs. !st exc st'. assign_tuple_target_list cx gs vs st = (INR exc,st') ==> no_control_exc exc`,
              `\cx es. T`]
  |> CONV_RULE (DEPTH_CONV BETA_CONV)
  |> PURE_REWRITE_RULE [FORALL_SIMP, AND_CLAUSES, IMP_CLAUSES];

Theorem tuple_store_no_control[local]:
  (!cx g v st exc st'. assign_tuple_targets cx g v st = (INR exc,st') ==>
    no_control_exc exc) /\
  (!cx gs vs st exc st'. assign_tuple_target_list cx gs vs st = (INR exc,st') ==>
    no_control_exc exc)
Proof
  ho_match_mp_tac tuple_no_control_ind >> rpt conj_tac >> NC_EVAL_CASE
QED

Theorem assign_tuple_targets_no_control:
  assign_tuple_targets cx g v st = (INR exc,st') ==> no_control_exc exc
Proof
  metis_tac[tuple_store_no_control]
QED

Theorem Send_outcome_runtime_error:
  (do
    (rq,outcome) <- take_call_outcome target [] (SOME amount);
    check outcome.co_success "send failed";
    adopt_call_outcome rq outcome;
    return (Value NoneV)
  od) st = (INR exc,st') ==>
  ?msg. exc = Error (RuntimeError msg)
Proof
  simp[checked_call_outcome_cases, return_def] >> rpt strip_tac
  >- (drule take_call_outcome_error >> rw[] >> simp[]) >> simp[]
QED
