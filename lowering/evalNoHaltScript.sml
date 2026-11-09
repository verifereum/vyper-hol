(* Source evaluation never halts (INR HaltException) on syntax without an
   expr_evm_run_root node (selfdestruct, delegate raw_call, create) when
   every internal call it makes is to the main module of a supported
   program.  Only selfdestruct raises the halt, and an internal call passes
   on its callee body's halt; external calls, send and raw_call surface a
   callee's halt as a successful call.
   TOP-LEVEL: eval_no_halt. *)
Theory evalNoHalt
Ancestors
  pair list rich_list sorting vyperAST vyperState vyperInterpreter
  vyperContext vyperMisc vyperValue vyperCallOutcome vyperCallOutcomeProps
  vyperStatePreservation vyperExprNoControl vyperCall vyperTypeCallGraph
  supportedExprTraverse supportedStmtTraverse supportedProgram
  bodyStorageCases
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

Theorem try_halt[local]:
  try f h s = (INR HaltException, s') ==>
  ?e t. f s = (INR e, t) /\ h e t = (INR HaltException, s')
Proof
  simp[try_def] >> Cases_on `f s` >>
  Cases_on `q` >> simp[]
QED

Theorem finally_halt[local]:
  finally f g s = (INR HaltException, s') ==>
  (?t. f s = (INR HaltException, t)) \/ (?t. g t = (INR HaltException, s'))
Proof
  simp[finally_def] >> Cases_on `f s` >>
  Cases_on `q` >> simp[ignore_bind_halt, return_def, raise_def] >>
  metis_tac[]
QED

Theorem finally_unless_halt_halt[local]:
  finally_unless_halt f g s = (INR HaltException, s') ==>
  (?t. f s = (INR HaltException, t)) \/ (?t. g t = (INR HaltException, s'))
Proof
  simp[finally_unless_halt_def] >> Cases_on `f s` >>
  Cases_on `q` >> simp[ignore_bind_halt, return_def]
  >- metis_tac[] >>
  Cases_on `y` >>
  simp[ignore_bind_halt, return_def, raise_def] >> metis_tac[]
QED

Theorem handle_function_halt[local]:
  handle_function e s = (INR HaltException, s') ==> e = HaltException
Proof
  Cases_on `e` >> simp[handle_function_def, return_def, raise_def]
QED

Theorem handle_loop_exception_halt[local]:
  handle_loop_exception e s = (INR HaltException, s') ==> e = HaltException
Proof
  rw[handle_loop_exception_def, return_def, raise_def]
QED

(* ===== Primitives that never halt ===== *)

Theorem return_nh[local]:
  return x s = (INR HaltException, s') ==> F
Proof
  simp[return_def]
QED

Theorem raise_nh[local]:
  raise e s = (INR HaltException, s') ==> e = HaltException
Proof
  simp[raise_def]
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
  (precompile_call_success bt s = (INR HaltException, s') ==> F) /\
  (frame_call_value cx vo s = (INR HaltException, s') ==> F) /\
  (take_call_outcome tg cd vo s = (INR HaltException, s') ==> F) /\
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
  >- simp[adopt_call_outcome_equation]
  >- (simp[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
           get_transient_storage_def, LET_THM, return_def] >>
      rw[raise_def, return_def, update_transient_def])
  >> simp[release_nonreentrant_lock_def, bind_def, get_transient_storage_def,
          update_transient_def, return_def]
QED

val nh_base = [bind_halt, ignore_bind_halt, return_nh, state_ops_nh,
               checks_nh, lifts_nh, storage_backend_nh, call_ops_nh,
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

Theorem places_nh[local]:
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

Theorem extend_place_nh[local]:
  extend_place cx pv sb s = (INR HaltException, s') ==> F
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      simp([extend_place_def, extend_storage_place_nh, places_nh] @ nh_base)) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  CASE_TAC >> simp nh_base
QED

Theorem select_result_nh[local]:
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

Theorem pop_place_nh[local]:
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

Theorem eval_ext_call_nh[local]:
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

Theorem guard_INL[local]:
  (type_check b m s = (INL x, t) <=> b /\ t = s) /\
  (check b m s = (INL x, t) <=> b /\ t = s) /\
  (lift_option_type xo m s = (INL v, t) <=> xo = SOME v /\ t = s) /\
  (lift_option xo m s = (INL v, t) <=> xo = SOME v /\ t = s)
Proof
  Cases_on `b` >> Cases_on `xo` >>
  simp[type_check_def, check_def, assert_def, lift_option_type_def,
       lift_option_def, return_def, raise_def, oneTheory.one] >>
  metis_tac[]
QED

Theorem get_module_code_stk_upd[local]:
  get_module_code (cx with stk updated_by f) src = get_module_code cx src
Proof
  simp[get_module_code_def]
QED

Theorem eval_exprs_nil_finally[local]:
  finally (do set_scopes sc; eval_exprs cx [] od) (set_scopes prev) s =
  (INL [], s with scopes := prev)
Proof
  simp[finally_def, ignore_bind_def, bind_def, set_scopes_def, return_def,
       Once evaluate_def]
QED

Theorem order_custom_error_args_exprs[local]:
  order_custom_error_args params err = SOME es ==> es = custom_error_exprs err
Proof
  Cases_on `err` >> rw[order_custom_error_args_def, custom_error_exprs_def] >>
  imp_res_tac order_custom_error_kwargs_SOME >> gvs[NULL_EQ]
QED

(* ===== Syntactic preconditions ===== *)

Theorem exprs_pre_every[local]:
  !es. EVERY (\e. ~supported_expr_exists p e /\ EVERY Q (int_calls_expr e)) es
       <=> ~supported_exprs_exists p es /\ EVERY Q (int_calls_exprs es)
Proof
  Induct >> simp[supported_expr_exists_def, int_calls_expr_def] >> metis_tac[]
QED

Theorem fields_exprs[local]:
  !kes. (supported_fields_exists p kes <=>
         supported_exprs_exists p (MAP SND kes)) /\
        int_calls_named_exprs kes = int_calls_exprs (MAP SND kes)
Proof
  Induct >- simp[supported_expr_exists_def, int_calls_expr_def] >>
  Cases >> simp[supported_expr_exists_def, int_calls_expr_def]
QED

val syn_ss = [supported_stmt_expr_exists_def, supported_expr_exists_def,
  supported_assignment_exists_def, supported_iterator_exists_def,
  supported_assert_exists_def, supported_raise_exists_def,
  expr_evm_run_root_def, int_calls_stmt_def, int_calls_expr_def,
  int_calls_atarget_def, int_calls_iterator_def, int_calls_assert_reason_def,
  int_calls_raise_reason_def, EVERY_APPEND, exprs_pre_every,
  fields_exprs, guard_INL, get_module_code_stk_upd];

val case_ss = nh_ss @ [raise_def];

val generic_tac =
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs[] >> metis_tac[];

val switch_tac =
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> drule switch_BoolV_halt >> simp case_ss >>
  rpt strip_tac >> gvs[] >> metis_tac[];

Theorem int_call_body_halt[local]:
  (!t t'. g t <> (INR HaltException, t')) /\
  finally_unless_halt
    (finally (try (do eval_stmts cxf ss; return NoneV od) handle_function)
       (pop_function prev)) g s =
    (INR HaltException, s') ==>
  ?t t'. eval_stmts cxf ss t = (INR HaltException, t')
Proof
  strip_tac >> drule finally_unless_halt_halt >> simp[] >> strip_tac >>
  drule finally_halt >> simp[state_ops_nh] >> strip_tac >>
  drule try_halt >> strip_tac >> imp_res_tac handle_function_halt >>
  gvs[ignore_bind_halt, return_def] >> metis_tac[]
QED

Theorem eval_no_halt_every[local]:
  (!cx s. ~supported_stmt_expr_exists expr_evm_run_root s /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_stmt s) ==>
     !st st'. eval_stmt cx s st = (INR HaltException, st') ==> F) /\
  (!cx ss. ~supported_stmts_expr_exists expr_evm_run_root ss /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_stmts ss) ==>
     !st st'. eval_stmts cx ss st = (INR HaltException, st') ==> F) /\
  (!cx it. ~supported_iterator_exists expr_evm_run_root it /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_iterator it) ==>
     !st st'. eval_iterator cx it st = (INR HaltException, st') ==> F) /\
  (!cx tyv nm ss vs. ~supported_stmts_expr_exists expr_evm_run_root ss /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_stmts ss) ==>
     !st st'. eval_for cx tyv nm ss vs st = (INR HaltException, st') ==> F) /\
  (!cx e. ~supported_expr_exists expr_evm_run_root e /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_expr e) ==>
     !st st'. eval_expr cx e st = (INR HaltException, st') ==> F) /\
  (!cx es. EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_expr e)) es ==>
     !st st'. eval_exprs cx es st = (INR HaltException, st') ==> F) /\
  (!cx t. ~supported_target_exists expr_evm_run_root t /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_target t) ==>
     !st st'. eval_base_place cx t st = (INR HaltException, st') ==> F) /\
  (!cx t. ~supported_target_exists expr_evm_run_root t /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_target t) ==>
     !st st'. eval_target_place cx t st = (INR HaltException, st') ==> F) /\
  (!cx g v. ~supported_assignment_exists expr_evm_run_root g /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_atarget g) ==>
     !st st'. assign_tuple_targets cx g v st = (INR HaltException, st') ==> F) /\
  (!cx gs vs. ~supported_assignments_exists expr_evm_run_root gs /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_atargets gs) ==>
     !st st'. assign_tuple_target_list cx gs vs st = (INR HaltException, st') ==>
              F) /\
  (!cx es. EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
     EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                get_module_code cx NONE = SOME tops) (int_calls_expr e)) es ==>
     !st st'. eval_expr_results cx es st = (INR HaltException, st') ==> F)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`Call _ (IntCall (src_id_opt,fn)) es _`] >- suspend "IntCall"
  >~ [`Call _ (ExtCall _ _ _ _) es _`] >- suspend "ExtCall"
  >~ [`Builtin _ bt es`] >- suspend "Builtin"
  >~ [`Raise (RaiseCustomError err)`] >- suspend "RaiseCustom"
  >~ [`Assert _ (AssertCustomError err)`] >- suspend "AssertCustom"
  >~ [`eval_for _ _ _ _ (_::_)`] >- suspend "ForCons"
  >~ [`Assign (TupleTarget _) _`] >- generic_tac
  >~ [`TupleTarget gs`] >- suspend "TupleTarget"
  >~ [`If _ _ _`] >- suspend "If"
  >~ [`Assert _ AssertBare`] >- switch_tac
  >~ [`Assert _ AssertUnreachable`] >- switch_tac
  >~ [`Assert _ (AssertReason _)`] >- switch_tac
  >~ [`IfExp _ _ _ _`] >- switch_tac
  >> generic_tac
QED

Resume eval_no_halt_every[If]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> drule finally_halt >> simp case_ss >> rpt strip_tac >>
  drule switch_BoolV_halt >> strip_tac >> metis_tac[]
QED

Resume eval_no_halt_every[TupleTarget]:
  rpt strip_tac >> pop_assum mp_tac >> simp[Once evaluate_def] >>
  Cases_on `v` >> simp[raise_def] >> CASE_TAC >> simp[raise_def] >>
  gvs syn_ss >> metis_tac[]
QED

Resume eval_no_halt_every[ForCons]:
  rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac
  >- (drule finally_halt >> simp case_ss >> rpt strip_tac >>
      drule try_halt >> strip_tac >> imp_res_tac handle_loop_exception_halt >>
      gvs case_ss >> metis_tac[]) >>
  rename1 `if broke then _ else _` >> Cases_on `broke` >> gvs case_ss >>
  metis_tac[]
QED

Resume eval_no_halt_every[RaiseCustom]:
  Cases_on `err` >> rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def, option_CASE_rator] @ case_ss) >> rpt strip_tac >>
  gvs([AllCaseEqs()] @ case_ss) >>
  imp_res_tac order_custom_error_args_exprs >>
  gvs(syn_ss @ case_ss) >> PairCases_on `p` >> gvs[] >>
  gvs[supported_exprs_exists_every, NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[]
QED

Resume eval_no_halt_every[AssertCustom]:
  Cases_on `err` >> rpt strip_tac >> pop_assum mp_tac >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> drule switch_BoolV_halt >>
  simp([option_CASE_rator] @ case_ss) >> rpt strip_tac >>
  gvs([AllCaseEqs()] @ case_ss) >>
  imp_res_tac order_custom_error_args_exprs >>
  gvs(syn_ss @ case_ss) >> PairCases_on `p` >> gvs[] >>
  gvs[supported_exprs_exists_every, NOT_EXISTS, combinTheory.o_DEF] >>
  metis_tac[]
QED

Resume eval_no_halt_every[Builtin]:
  rpt strip_tac >> pop_assum mp_tac >>
  Cases_on `bt = Len` >> Cases_on `bt = Env MsgGas` >>
  Cases_on `bt = Bop In \/ bt = Bop NotIn` >>
  simp([Once evaluate_def, COND_RATOR] @ case_ss) >>
  gvs(syn_ss @ case_ss) >> rpt strip_tac >>
  gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
  gvs(syn_ss @ case_ss) >> metis_tac[]
QED

Resume eval_no_halt_every[ExtCall]:
  rpt strip_tac >> pop_assum mp_tac >> gvs syn_ss >>
  `EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
          EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                     get_module_code cx NONE = SOME tops) (int_calls_expr e)) es` by gvs[exprs_pre_every] >>
  `!n. EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
          EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                     get_module_code cx NONE = SOME tops) (int_calls_expr e)) (TAKE n es) /\
       EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
          EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                     get_module_code cx NONE = SOME tops) (int_calls_expr e)) (DROP n es) /\
       EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
          EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                     get_module_code cx NONE = SOME tops) (int_calls_expr e)) (TAKE n (DROP 1 es))` by
    metis_tac[EVERY_TAKE, EVERY_DROP] >>
  simp([Once evaluate_def] @ case_ss) >> gvs(syn_ss @ case_ss) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume eval_no_halt_every[IntCall]:
  strip_tac >> simp syn_ss >> strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[] >>
  Cases_on `MEM (NONE,fn) cx.stk`
  >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, ignore_bind_def,
           bind_def, raise_def]) >>
  Cases_on `lookup_callable_function cx.in_deploy fn tops`
  >- (rpt (qpat_x_assum `!x. _` kall_tac) >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
           return_def, raise_def, ignore_bind_def, bind_def]) >>
  rename1 `_ = SOME tup` >> PairCases_on `tup` >>
  drule_all supported_callable_storage_syntax >> strip_tac >> gvs[] >>
  Cases_on `LENGTH es = LENGTH tup2`
  >- suspend "IntCallLive" >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, type_check_def, assert_def, lift_option_type_def,
       return_def, raise_def, ignore_bind_def, bind_def]
QED

Resume eval_no_halt_every[IntCallLive]:
  drule_all eval_expr_intcall_empty_defaults >>
  disch_then (fn th => qpat_x_assum `eval_expr _ _ _ = _`
    (mp_tac o REWRITE_RULE [th])) >>
  gvs(syn_ss @ case_ss @ [eval_exprs_nil_finally, push_function_def,
                          get_scopes_def]) >>
  rpt strip_tac >> drule_at Any int_call_body_halt >>
  impl_tac >- (rw[] >> rpt CASE_TAC >> simp case_ss) >>
  strip_tac >> metis_tac[]
QED

Finalise eval_no_halt_every

Theorem calls_pre_every[local]:
  (l = [] \/ ?tops. supported_program tops /\
                    get_module_code cx NONE = SOME tops /\
                    EVERY (\c. FST c = NONE) l) ==>
  EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                                    get_module_code cx NONE = SOME tops) l
Proof
  rw[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

(* Evaluation never halts (SELFDESTRUCT is the only source of HaltException)
   when no evm-run root occurs and every internal call goes to a supported
   program of the current module. *)
Theorem eval_no_halt:
  (!cx e st st'.
     ~supported_expr_exists expr_evm_run_root e /\
     (int_calls_expr e = [] \/
      ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
             EVERY (\c. FST c = NONE) (int_calls_expr e)) ==>
     eval_expr cx e st <> (INR HaltException, st')) /\
  (!cx es st st'.
     ~supported_exprs_exists expr_evm_run_root es /\
     (int_calls_exprs es = [] \/
      ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
             EVERY (\c. FST c = NONE) (int_calls_exprs es)) ==>
     eval_exprs cx es st <> (INR HaltException, st')) /\
  (!cx s st st'.
     ~supported_stmt_expr_exists expr_evm_run_root s /\
     (int_calls_stmt s = [] \/
      ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
             EVERY (\c. FST c = NONE) (int_calls_stmt s)) ==>
     eval_stmt cx s st <> (INR HaltException, st')) /\
  (!cx ss st st'.
     ~supported_stmts_expr_exists expr_evm_run_root ss /\
     (int_calls_stmts ss = [] \/
      ?tops. supported_program tops /\ get_module_code cx NONE = SOME tops /\
             EVERY (\c. FST c = NONE) (int_calls_stmts ss)) ==>
     eval_stmts cx ss st <> (INR HaltException, st'))
Proof
  rpt conj_tac >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
                (assume_tac o MATCH_MP calls_pre_every))
  >- metis_tac[cj 5 eval_no_halt_every]
  >- (`EVERY (\e. ~supported_expr_exists expr_evm_run_root e /\
         EVERY (\c. FST c = NONE /\ ?tops. supported_program tops /\
                    get_module_code cx NONE = SOME tops) (int_calls_expr e)) es`
        by simp[exprs_pre_every] >>
      metis_tac[cj 6 eval_no_halt_every])
  >- metis_tac[cj 1 eval_no_halt_every] >>
  metis_tac[cj 2 eval_no_halt_every]
QED
