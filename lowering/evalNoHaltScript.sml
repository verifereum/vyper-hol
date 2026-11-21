(* Source evaluation never halts (INR HaltException) on syntax without an
   expr_halt_root node (selfdestruct or create) when
   every internal call it makes is to the main module of a supported
   program.  Only selfdestruct raises the halt, and an internal call passes
   on its callee body's halt; external calls, send and raw_call surface a
   callee's halt as a successful call.
   TOP-LEVEL: eval_no_halt, external_body_no_halt. *)
Theory evalNoHalt
Ancestors
  pair list rich_list sorting vyperAST vyperState vyperInterpreter
  vyperContext vyperMisc vyperValue vyperCallOutcome vyperCallOutcomeProps
  vyperStatePreservation vyperExprNoControl vyperCall vyperTypeCallGraph
  supportedExprTraverse supportedStmtTraverse supportedDecls supportedProgram
  bodyStorageCases vyperGetter vyperTypeContractGetter vyperTypeContractSoundness
  vyperCreateFrame vyperCallOutcomeFrame
Libs
  pairLib monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";
val _ = overload_on ("bind", ``vyperState$bind``);
val _ = overload_on ("return", ``vyperState$return``);
val _ = overload_on ("ignore_bind", ``vyperState$ignore_bind``);
val _ = overload_on ("raise", ``vyperState$raise``);
val _ = overload_on ("try", ``vyperState$try``);
val _ = overload_on ("finally", ``vyperState$finally``);

(* ===== Monadic composition ===== *)

Theorem bind_halt[local]:
  bind f g s = (INR HaltException, s') <=>
  f s = (INR HaltException, s') \/
  ?x t. f s = (INL x, t) /\ g x t = (INR HaltException, s')
Proof
  simp[bind_def] >> Cases_on `f s` >>
  Cases_on `q` >> simp[]
QED

Theorem ignore_bind_halt[local]:
  ignore_bind f g s = (INR HaltException, s') <=>
  f s = (INR HaltException, s') \/
  ?x t. f s = (INL x, t) /\ g t = (INR HaltException, s')
Proof
  simp[ignore_bind_def, bind_halt]
QED

(* ===== Primitives that never halt ===== *)

Theorem return_nh[local]:
  return x s = (INR HaltException, s') ==> F
Proof
  simp[return_def]
QED

Theorem state_ops_nh[local]:
  (get_scopes s = (INR HaltException, s') ==> F) /\
  (set_scopes sc s = (INR HaltException, s') ==> F) /\
  (push_scope s = (INR HaltException, s') ==> F) /\
  (push_scope_with_var nm tv v s = (INR HaltException, s') ==> F) /\
  (pop_scope s = (INR HaltException, s') ==> F) /\
  (get_accounts s = (INR HaltException, s') ==> F) /\
  (update_accounts fa s = (INR HaltException, s') ==> F) /\
  (get_transient_storage s = (INR HaltException, s') ==> F) /\
  (update_transient ft s = (INR HaltException, s') ==> F) /\
  (update_pending_deletions fd s = (INR HaltException, s') ==> F) /\
  (push_log lg s = (INR HaltException, s') ==> F) /\
  (append_logs lgs s = (INR HaltException, s') ==> F) /\
  (pop_function prev s = (INR HaltException, s') ==> F) /\
  (push_function sf env cx s = (INR HaltException, s') ==> F)
Proof
  simp[get_scopes_def, set_scopes_def, push_scope_def,
       push_scope_with_var_def, get_accounts_def, update_accounts_def,
       get_transient_storage_def, update_transient_def,
       update_pending_deletions_def, push_log_def, append_logs_def,
       pop_function_def, push_function_def, return_def] >>
  simp[pop_scope_def] >> CASE_TAC >> simp[return_def, raise_def]
QED

Theorem checks_nh[local]:
  (check b m s = (INR HaltException, s') ==> F) /\
  (type_check b m s = (INR HaltException, s') ==> F) /\
  (check_not_static cx s = (INR HaltException, s') ==> F)
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem lifts_nh[local]:
  (lift_option xo m s = (INR HaltException, s') ==> F) /\
  (lift_option_type xo m s = (INR HaltException, s') ==> F) /\
  (lift_sum xs s = (INR HaltException, s') ==> F) /\
  (lift_sum_runtime xr s = (INR HaltException, s') ==> F)
Proof
  Cases_on `xo` >> Cases_on `xs` >> Cases_on `xr` >>
  simp[lift_option_def, lift_option_type_def, lift_sum_def,
       lift_sum_runtime_def, return_def, raise_def]
QED

Theorem storage_backend_nh[local]:
  (get_storage_backend cx tr s = (INR HaltException, s') ==> F) /\
  (set_storage_backend cx tr sto s = (INR HaltException, s') ==> F)
Proof
  Cases_on `tr` >>
  simp[get_storage_backend_def, set_storage_backend_def, bind_def,
       get_transient_storage_def, update_transient_def, get_accounts_def,
       update_accounts_def, return_def]
QED

Theorem call_ops_nh[local]:
  (next_gas_reading s = (INR HaltException, s') ==> F) /\
  (precompile_call_success bt vs s = (INR HaltException, s') ==> F) /\
  (frame_call_value cx vo s = (INR HaltException, s') ==> F) /\
  (take_call_outcome gas_cap tg cd vo s = (INR HaltException, s') ==> F) /\
  (take_delegate_outcome gas_cap tg cd vo s = (INR HaltException, s') ==> F) /\
  (adopt_call_outcome rq oc s = (INR HaltException, s') ==> F) /\
  (acquire_nonreentrant_lock a sl iv s = (INR HaltException, s') ==> F) /\
  (release_nonreentrant_lock a sl s = (INR HaltException, s') ==> F)
Proof
  rpt conj_tac
  >- (strip_tac >> gvs[next_gas_reading_def, AllCaseEqs(), return_def, raise_def])
  >- (strip_tac >> drule precompile_call_success_exception >> simp[])
  >- (Cases_on `cx.txn.is_static` >>
      simp[frame_call_value_def, ignore_bind_def, bind_def, check_def,
           assert_def, return_def] >> rw[])
  >- (strip_tac >> drule take_call_outcome_error >> simp[])
  >- (strip_tac >> drule take_delegate_outcome_error >> simp[])
  >- simp[adopt_call_outcome_equation]
  >- (simp[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
           record_storage_event_def,
           get_transient_storage_def, LET_THM, return_def] >>
      rw[raise_def, return_def, update_transient_def])
  >> simp[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
          record_storage_event_def, get_transient_storage_def,
          update_transient_def, return_def]
QED

val nh_base = [bind_halt, ignore_bind_halt, return_nh, state_ops_nh,
               checks_nh, lifts_nh, storage_backend_nh, call_ops_nh,
               record_storage_event_def, record_storage_backend_def,
               return_def, LET_THM, FORALL_PROD, EXISTS_PROD];

Theorem lock_nh[local]:
  (lock_if_nr cx nr iv s = (INR HaltException, s') ==> F) /\
  (unlock_if_nr cx nr iv s = (INR HaltException, s') ==> F)
Proof
  Cases_on `nr` >> Cases_on `iv` >> Cases_on `cx.nonreentrant_slot` >>
  simp([raise_def] @ nh_base)
QED

Theorem storage_slot_nh[local]:
  (read_storage_slot cx tr slot tv s = (INR HaltException, s') ==> F) /\
  (write_storage_slot cx tr slot tv v s = (INR HaltException, s') ==> F)
Proof
  simp([read_storage_slot_def, write_storage_slot_def] @ nh_base)
QED

Theorem immutables_nh[local]:
  (get_immutables cx src s = (INR HaltException, s') ==> F) /\
  (set_immutable cx src n tv v s = (INR HaltException, s') ==> F)
Proof
  simp([get_immutables_def, get_address_immutables_def, set_immutable_def,
        set_address_immutables_def] @ nh_base)
QED

Theorem lookup_global_nh[local]:
  lookup_global cx src n s = (INR HaltException, s') ==> F
Proof
  strip_tac >>
  gvs([lookup_global_def, immutables_nh, AllCaseEqs(), option_CASE_rator,
       prod_CASE_rator, var_decl_info_CASE_rator, raise_def] @ nh_base)
QED

Theorem lookup_flag_mem_nh[local]:
  lookup_flag_mem cx nsid mid s = (INR HaltException, s') ==> F
Proof
  Cases_on `nsid` >> strip_tac >>
  gvs[lookup_flag_mem_def, AllCaseEqs(), option_CASE_rator, return_def,
      raise_def]
QED

Theorem resolve_array_element_nh[local]:
  !cx tr slot tv subs s s'.
    resolve_array_element cx tr slot tv subs s = (INR HaltException, s') ==> F
Proof
  ho_match_mp_tac resolve_array_element_ind >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> rpt gen_tac >>
      simp([Once resolve_array_element_def] @ nh_base) >> conj_tac
      >- (Cases_on `bd` >> simp nh_base) >>
      rpt strip_tac >> metis_tac[]) >>
  simp[Once resolve_array_element_def, return_def, raise_def]
QED

Theorem places_nh:
  (read_place cx p s = (INR HaltException, s') ==> F) /\
  (place_type_value cx p s = (INR HaltException, s') ==> F) /\
  (write_place cx p v s = (INR HaltException, s') ==> F)
Proof
  Cases_on `p` >>
  simp([read_place_def, place_type_value_def, write_place_def,
        storage_slot_nh, immutables_nh] @ nh_base)
QED

Theorem read_result_no_halt:
  read_result cx tv s = (INR HaltException, s') ==> F
Proof
  Cases_on `tv` >> simp[read_result_def, return_def, raise_def, places_nh]
QED

Theorem read_results_nh[local]:
  !rs s s'. read_results cx rs s = (INR HaltException, s') ==> F
Proof
  Induct >> simp([read_results_def, read_result_no_halt] @ nh_base)
QED

Theorem extend_storage_place_nh[local]:
  extend_storage_place cx tr slot tv sb s = (INR HaltException, s') ==> F
Proof
  Cases_on `tv` >> Cases_on `sb` >>
  simp([extend_storage_place_def, raise_def, resolve_array_element_nh] @
       nh_base) >>
  rename1 `ValueSubscript v` >> Cases_on `v` >>
  simp([extend_storage_place_def, raise_def, resolve_array_element_nh] @
       nh_base)
QED

Theorem extend_place_nh:
  extend_place cx pv sb s = (INR HaltException, s') ==> F
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      simp([extend_place_def, extend_storage_place_nh, places_nh] @ nh_base)) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  CASE_TAC >> simp nh_base
QED

Theorem select_result_nh:
  select_result cx ty pv sb s = (INR HaltException, s') ==> F
Proof
  Cases_on `pv` >> simp([select_result_def, extend_place_nh] @ nh_base)
QED

Theorem get_place_nh[local]:
  get_place pv s = (INR HaltException, s') ==> F
Proof
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def]
QED

Theorem conditional_result_nh[local]:
  conditional_result cx pv s = (INR HaltException, s') ==> F
Proof
  Cases_on `pv` >> simp([conditional_result_def, raise_def, places_nh] @ nh_base) >>
  rw[] >> simp([places_nh] @ nh_base)
QED

Theorem result_array_length_nh[local]:
  !cx tv s s'. result_array_length cx tv s = (INR HaltException, s') ==> F
Proof
  ho_match_mp_tac result_array_length_ind >> rpt gen_tac >>
  simp([result_array_length_def, read_result_no_halt] @ nh_base) >>
  rpt strip_tac >> rename1 `read_result _ _ _ = (INL v, _)` >>
  Cases_on `v` >> gvs[return_def, raise_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[return_def]
QED

Theorem pop_place_nh:
  !cx p s s'. pop_place cx p s = (INR HaltException, s') ==> F
Proof
  ho_match_mp_tac pop_place_ind >> rpt gen_tac >>
  simp([pop_place_def, raise_def, storage_slot_nh, immutables_nh] @ nh_base)
QED

Theorem append_place_nh[local]:
  !cx p v s s'. append_place cx p v s = (INR HaltException, s') ==> F
Proof
  ho_match_mp_tac append_place_ind >> rpt gen_tac >>
  simp([append_place_def, storage_slot_nh, places_nh] @ nh_base)
QED

Theorem new_variable_nh[local]:
  new_variable id tv v s = (INR HaltException, s') ==> F
Proof
  simp([new_variable_def] @ nh_base) >> rpt strip_tac >>
  rename1 `get_scopes _ = (INL sc, _)` >> Cases_on `sc` >>
  gvs([raise_def] @ nh_base)
QED

Theorem array_iterator_results_nh[local]:
  array_iterator_results cx ty res s = (INR HaltException, s') ==> F
Proof
  Cases_on `res` >>
  TRY (rename1 `PlaceR p` >> Cases_on `p` >>
       TRY (rename1 `StoragePlace tr slot tv` >> Cases_on `tv`)) >>
  simp([array_iterator_results_def, read_result_no_halt, result_array_length_nh] @
       nh_base)
QED

Theorem switch_BoolV_halt[local]:
  switch_BoolV cx tv f g s = (INR HaltException, s') ==>
  ?t. f t = (INR HaltException, s') \/ g t = (INR HaltException, s')
Proof
  simp([switch_BoolV_def, read_result_no_halt] @ nh_base) >> rpt strip_tac >>
  rename1 `read_result _ _ _ = (INL v, t)` >>
  Cases_on `v = BoolV T` >> Cases_on `v = BoolV F` >> gvs[raise_def] >>
  metis_tac[]
QED

(* ===== Calls ===== *)

Theorem eval_ext_call_effects_nh[local]:
  eval_ext_call_effects cx target calldata vo gas accounts s =
    (INR HaltException, s') ==> F
Proof
  strip_tac >>
  gvs([eval_ext_call_effects_def, AllCaseEqs(), option_CASE_rator,
       COND_RATOR, raise_def] @ nh_base)
QED

Theorem eval_ext_call_nh:
  eval_ext_call cx static skip_check sg opts vs s =
    (INR HaltException, s') ==> F
Proof
  PairCases_on `sg` >> Cases_on `vs` >>
  simp[eval_ext_call_def, raise_def] >> strip_tac >>
  gvs([eval_ext_call_effects_nh, AllCaseEqs(), option_CASE_rator,
       COND_RATOR, raise_def] @ nh_base)
QED

Theorem eval_send_nh[local]:
  eval_send cx has_gas vs s = (INR HaltException, s') ==> F
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def] >>
  rename1 `_ :: rest` >> Cases_on `rest` >- simp[eval_send_def, raise_def] >>
  simp[eval_send_def] >> strip_tac >>
  gvs([AllCaseEqs(), option_CASE_rator, raise_def] @ nh_base)
QED

Theorem eval_raw_call_nh[local]:
  eval_raw_call cx flags target calldata amount gas s =
    (INR HaltException, s') ==> F
Proof
  strip_tac >>
  gvs([eval_raw_call_def, AllCaseEqs(), COND_RATOR, raise_def] @ nh_base)
QED

val nh_ss = nh_base @ [lock_nh, storage_slot_nh, immutables_nh,
  lookup_global_nh, lookup_flag_mem_nh, places_nh, read_result_no_halt,
  read_results_nh, extend_place_nh, select_result_nh, get_place_nh,
  conditional_result_nh, result_array_length_nh, pop_place_nh,
  append_place_nh, new_variable_nh, array_iterator_results_nh,
  eval_ext_call_nh, eval_send_nh, eval_raw_call_nh];

(* A halt in a newly created account carries its scheduled deletion. *)
Theorem finally_halt_pending[local]:
  finally f g s = (INR HaltException, t) /\
  (!a a'. g a <> (INR HaltException,a')) /\
  (!a a'. g a = (INL (),a') ==> a'.pending_deletions = a.pending_deletions) ==>
  ?a. f s = (INR HaltException,a) /\
      t.pending_deletions = a.pending_deletions
Proof
  Cases_on `f s` >> Cases_on `q` >>
  rw[finally_def, ignore_bind_halt, return_def, raise_def] >>
  metis_tac[oneTheory.one]
QED

Theorem finally_unless_halt_exact[local]:
  finally_unless_halt f g s = (INR HaltException,t) /\
  (!a a'. g a <> (INR HaltException,a')) ==>
  f s = (INR HaltException,t)
Proof
  Cases_on `f s` >> Cases_on `q` >>
  simp[finally_unless_halt_def, ignore_bind_halt, return_def]
  >- metis_tac[] >>
  Cases_on `y` >> simp[ignore_bind_halt, raise_def] >> metis_tac[]
QED

Theorem try_handlers_halt[local]:
  (try f handle_function s = (INR HaltException,t) <=> f s = (INR HaltException,t)) /\
  (try g handle_loop_exception s = (INR HaltException,t) <=>
     g s = (INR HaltException,t))
Proof
  conj_tac
  >- (Cases_on `f s` >> Cases_on `q` >> simp[try_def] >>
      Cases_on `y` >> simp[handle_function_def, return_def, raise_def]) >>
  Cases_on `g s` >> Cases_on `q` >>
  simp[try_def] >>
  Cases_on `y` >> simp[handle_loop_exception_def, return_def, raise_def]
QED

Theorem cleanup_preserves_pending[local]:
  (pop_scope s = (INL (),t) ==> t.pending_deletions = s.pending_deletions) /\
  (pop_function prev s = (INL (),t) ==> t.pending_deletions = s.pending_deletions) /\
  (set_scopes scopes s = (INL (),t) ==> t.pending_deletions = s.pending_deletions)
Proof
  Cases_on `s.scopes` >>
  rw[pop_scope_def, pop_function_def, set_scopes_def, return_def, raise_def] >>
  gvs[]
QED

Theorem halt_pending_transfer[local]:
  vyperInterpreter$transfer_value src dst amount s = (INR HaltException,s') ==> F
Proof
  Cases_on `amount = 0 \/ src = dst` >>
  simp[vyperInterpreterTheory.transfer_value_def, ignore_bind_halt, bind_halt,
       return_def, state_ops_nh, checks_nh]
QED

Theorem create_operands_nh[local]:
  eval_create_operands cx kind has_salt rof tys offset vs s = (INR HaltException,s') ==> F
Proof
  `!ts v size st. eval_create cx kind has_salt rof ts v size st =
      (INR HaltException,s') ==> F` by
    (rpt strip_tac >> drule eval_create_exception_is_error >> simp[]) >>
  Cases_on `kind` >> simp[vyperCreateTheory.eval_create_operands_def, LET_THM, bind_halt] >>
  rpt strip_tac >> drule check_create_blueprint_exception_is_error >> simp[]
QED

val pending_ss = nh_ss @
  [try_handlers_halt, halt_pending_transfer, create_operands_nh,
   raise_def];

val pending_generic_tac =
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def, COND_RATOR] @ pending_ss) >>
  rpt strip_tac >> gvs pending_ss >>
  TRY (first_assum (fn th => first_assum (ACCEPT_TAC o MATCH_MP th)));

val apply_pending_hyp_tac =
  first_assum (fn th => first_assum (ACCEPT_TAC o MATCH_MP th));

val staged_pending_ih =
  first_assum (fn th =>
    drule_all_then (fn step =>
      ACCEPT_TAC step ORELSE drule_all_then ACCEPT_TAC step) th);

val cleanup_pending_tac =
  drule finally_halt_pending >>
  simp[state_ops_nh, cleanup_preserves_pending, ignore_bind_halt, return_def,
       try_handlers_halt] >>
  strip_tac >> gvs[] >>
  TRY (drule switch_BoolV_halt >> simp pending_ss >> strip_tac >> gvs[]) >>
  staged_pending_ih;


Theorem internal_body_pending_cleanup[local]:
  (!a a'. cleanup a <> (INR HaltException,a')) /\
  finally_unless_halt
    (finally (try (ignore_bind (eval_stmts cxf ss) (return NoneV))
       handle_function) (pop_function prev)) cleanup s = (INR HaltException,t) ==>
  ?u. eval_stmts cxf ss s = (INR HaltException,u) /\
      t.pending_deletions = u.pending_deletions
Proof
  strip_tac >> drule_all finally_unless_halt_exact >> strip_tac >>
  drule finally_halt_pending >>
  simp[state_ops_nh, cleanup_preserves_pending, try_handlers_halt,
       ignore_bind_halt, return_def] >>
  metis_tac[cleanup_preserves_pending]
QED

Theorem internal_defaults_pending_cleanup[local]:
  finally (ignore_bind (set_scopes sc) f) (set_scopes prev) s =
    (INR HaltException,t) ==>
  ?a u. set_scopes sc s = (INL (),a) /\ f a = (INR HaltException,u) /\
        t.pending_deletions = u.pending_deletions
Proof
  strip_tac >> drule finally_halt_pending >>
  simp[state_ops_nh, cleanup_preserves_pending, ignore_bind_halt] >>
  impl_tac >- metis_tac[CONJUNCT2 (CONJUNCT2 cleanup_preserves_pending)] >>
  strip_tac >> qexistsl_tac [`t'`, `a`] >> simp[]
QED

fun last_premise tm =
  let val (p,q) = dest_imp (#2 (strip_forall tm)) in
    if is_imp (#2 (strip_forall q)) then last_premise q else p
  end;

val pending_tuple_target_tac =
  rpt strip_tac >> pop_assum mp_tac >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[raise_def] >> CASE_TAC >> simp[raise_def] >>
  strip_tac >> TRY staged_pending_ih;

fun apply_trace_ih th =
  let
    val simplified = SIMP_RULE (srw_ss()) [] th
    val body = #2 (strip_forall (concl simplified))
  in
    if is_imp body then
      first_assum (mp_then (Pos hd) apply_trace_ih simplified)
    else
      ACCEPT_TAC simplified
  end;

Theorem eval_halt_pending[local]:
  (!cx x s t. cx.txn.created_in_tx /\ eval_stmt cx x s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx xs s t. cx.txn.created_in_tx /\ eval_stmts cx xs s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx x s t. cx.txn.created_in_tx /\ eval_iterator cx x s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx ty id xs vs s t. cx.txn.created_in_tx /\ eval_for cx ty id xs vs s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx x s t. cx.txn.created_in_tx /\ eval_expr cx x s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx xs s t. cx.txn.created_in_tx /\ eval_exprs cx xs s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx x s t. cx.txn.created_in_tx /\ eval_base_place cx x s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx x s t. cx.txn.created_in_tx /\ eval_target_place cx x s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx x v s t. cx.txn.created_in_tx /\ assign_tuple_targets cx x v s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions) /\
  (!cx xs vs s t. cx.txn.created_in_tx /\ assign_tuple_target_list cx xs vs s = (INR HaltException,t) ==>
      MEM cx.txn.target t.pending_deletions)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  (fn (g as (_,w)) =>
    if can (find_term (same_const ``IntCall``)) w then ALL_TAC g
    else if can (find_term (can (match_term ``assign_tuple_targets cx
                    (TupleTarget xs) v st``))) (last_premise w)
    then pending_tuple_target_tac g
    else pending_generic_tac g) >>
  TRY (drule_then strip_assume_tac switch_BoolV_halt >> gvs pending_ss) >>
  TRY (qpat_assum `(case err of CustomError _ _ _ => _) _ = _` (K ALL_TAC) >>
       Cases_on `err` >> PairCases_on `p` >> gvs[AllCaseEqs(), option_CASE_rator] >>
       gvs pending_ss >> TRY apply_pending_hyp_tac) >>
  TRY apply_pending_hyp_tac >>
  TRY (qpat_assum `ignore_bind (update_accounts _) _ _ = (INR HaltException,_)`
         (mp_tac) >>
       simp[ignore_bind_halt,state_ops_nh, update_pending_deletions_def,
            raise_def, update_accounts_def, return_def] >> strip_tac >> gvs[]) >>
  TRY (gvs[update_pending_deletions_def,return_def] >> NO_TAC) >>
  TRY staged_pending_ih >>
  TRY (cleanup_pending_tac >> NO_TAC) >>
  TRY (qpat_assum `(if broke then _ else _) = _` (K ALL_TAC) >>
       Cases_on `broke` >> gvs pending_ss >> staged_pending_ih) >>
  TRY (qpat_assum `(if subscript_reads_base cx x x' then _ else _) = _`
         (K ALL_TAC) >>
       Cases_on `subscript_reads_base cx x x'` >> gvs pending_ss >>
       TRY staged_pending_ih) >>
  TRY (qpat_assum `(case v of ArrayV _ => _ | _ => _) _ = _` (K ALL_TAC) >>
       Cases_on `v` >> gvs pending_ss >> CASE_TAC >> gvs pending_ss >>
       staged_pending_ih) >>
  TRY (qpat_assum `(if bt = Len then _ else _) = _` (K ALL_TAC) >>
       Cases_on `bt = Len` >> Cases_on `bt = Env MsgGas` >> gvs pending_ss >>
       TRY (Cases_on `code_slice_source bt xs` >> gvs pending_ss >>
         TRY (PairCases_on `x` >> gvs pending_ss)) >>
       TRY staged_pending_ih) >>
  TRY (qpat_x_assum `ignore_bind (update_accounts _) _ _ = (INL (),_)` mp_tac >>
       simp[ignore_bind_def, bind_def, update_accounts_def,
            update_pending_deletions_def, return_def] >> strip_tac >> gvs[]) >>
  TRY (first_assum (fn th =>
      if can (find_term (same_const ``assign_tuple_target_list``)) (concl th)
         andalso is_eq (concl th)
      then mp_tac th else NO_TAC) >>
    simp[value_CASE_rator, array_value_CASE_rator, AllCaseEqs(), raise_def] >>
    strip_tac >> gvs[] >> staged_pending_ih) >>
  TRY (rpt strip_tac >>
    qpat_x_assum `eval_expr cx (Call _ (IntCall _) _ _) _ = _` mp_tac >>
    simp_tac std_ss ([Once evaluate_def] @ pending_ss) >>
    rpt strip_tac >>
    TRY staged_pending_ih >>
    TRY (drule internal_defaults_pending_cleanup >> strip_tac) >>
    TRY (drule internal_body_pending_cleanup >>
       impl_tac >- metis_tac[CONJUNCT2 lock_nh] >> strip_tac)) >>
  TRY (drule (CONJUNCT1 lock_nh) >> simp[]) >>
  TRY (drule_at (Pos last) internal_body_pending_cleanup >>
    impl_tac >- metis_tac[CONJUNCT2 lock_nh] >> strip_tac) >>
  TRY (qpat_assum `push_function _ _ _ _ = (INL cxf,_)`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [push_function_def, return_def])) >>
  TRY (qpat_x_assum `t.pending_deletions = u.pending_deletions` SUBST1_TAC) >>
  TRY (qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
    (K ALL_TAC) >>
    Cases_on `(x:unit)` >> Cases_on `(x':unit)` >> Cases_on `(x'':unit)` >>
    TRY (qpat_x_assum `cx with stk updated_by _ = cxf` (SUBST_ALL_TAC o SYM)) >>
    TRY (qpat_x_assum `t.pending_deletions = u.pending_deletions` SUBST1_TAC) >>
    first_assum (fn th =>
      if is_forall (concl th)
      then drule_all_then (ACCEPT_TAC o SIMP_RULE (srw_ss()) [])
        (SIMP_RULE (srw_ss()) [] th)
      else NO_TAC)) >>
  TRY (qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
    (K ALL_TAC) >>
    rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
    TRY staged_pending_ih) >>
  TRY (qpat_assum `assign_tuple_target_list _ _ _ _ = (INR HaltException,_)`
    (K ALL_TAC) >> gvs[] >> metis_tac[]) >>
  TRY (qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
    (K ALL_TAC) >> first_assum (fn th =>
      if is_forall (concl th) then apply_trace_ih th else NO_TAC)) >>
  TRY (qpat_x_assum `cx with stk updated_by _ = cxf` (SUBST_ALL_TAC o SYM) >>
    rule_assum_tac (SIMP_RULE (srw_ss()) []) >>
    first_assum (fn th =>
      if is_forall (concl th) then apply_trace_ih th else NO_TAC))
QED

Theorem eval_stmts_halt_pending_deletions:
  eval_stmts cx ss s = (INR HaltException,t) ==>
  cx.txn.created_in_tx ==> MEM cx.txn.target t.pending_deletions
Proof
  metis_tac[CONJUNCT1 (CONJUNCT2 eval_halt_pending)]
QED
