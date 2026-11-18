Theory vyperInterpreterCV
Ancestors
  vyperCallOutcome[ignore_grammar]
  arithmetic alist combin option list finite_map pair
  rich_list sorting cv cv_std vfmState vfmContext vfmCompute[ignore_grammar]
  vfmExecution[ignore_grammar] vyperAST vyperGetter vyperABI
  vyperMisc vyperNsidFmap vyperValue vyperValueOperation vyperStorage vyperContext vyperState
  vyperEvent vyperEvmBoundary vyperCreate vyperRuntimeAccounts
  vyperSubscriptOverlap
  vyperInterpreter vyperSubscriptOverlapCV
Libs
  cv_transLib wordsLib intLib monadsyntax

(* These became simp rules after their original inline translations. *)
val () = temp_delsimps ["lock_if_nr_def", "unlock_if_nr_def"];

val () = cv_auto_trans push_function_def;

val () = cv_auto_trans pop_function_def;

val () = transfer_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR, update_accounts_def, o_DEF, C_DEF]
  |> cv_auto_trans;

val () = cv_auto_trans lookup_function_def;

val () = cv_auto_trans lookup_callable_function_def;

val () = cv_auto_trans lookup_raw_return_def;

val () = cv_auto_trans lookup_raw_return_or_F_def;

val bind_arguments_pre_def = cv_auto_trans_pre "bind_arguments_pre" bind_arguments_def;

Theorem bind_arguments_pre[cv_pre]:
  ∀x y z. bind_arguments_pre x y z
Proof
  ho_match_mp_tac bind_arguments_ind \\ rw[]
  \\ rw[Once bind_arguments_pre_def]
QED

val () = handle_function_def
  |> SRULE [FUN_EQ_THM]
  |> cv_auto_trans;

val () = cv_auto_trans subscript_reads_base_def;

val () = handle_loop_exception_def
  |> SRULE [FUN_EQ_THM, COND_RATOR]
  |> cv_auto_trans;

val () = cv_auto_trans is_immutable_decl_def;

val () = cv_auto_trans get_range_limits_def;

val () = cv_auto_trans make_ext_call_state_def;

val () = cv_auto_trans extract_call_result_def;

val () = cv_auto_trans ext_call_value_transfer_ok_def;

val () = cv_auto_trans ext_call_success_accounts_ok_aux_def;

val () = cv_auto_trans run_ext_call_def;

val () = cv_auto_trans forwarded_gas_def;

val () = cv_auto_trans make_delegate_call_state_def;

val () = cv_auto_trans run_delegate_call_def;

val () = cv_auto_trans run_raw_call_def;

val () = cv_auto_trans ext_call_has_code_def;

val () = cv_auto_trans ext_call_precheck_ok_def;

val () = frame_call_value_def
  |> SRULE [FUN_EQ_THM, COND_RATOR, ignore_bind_def, bind_def, check_def,
            assert_def]
  |> cv_auto_trans;

val () = eval_raw_call_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, UNCURRY,
            COND_RATOR, prod_CASE_rator, sum_CASE_rator, lift_option_def,
            option_CASE_rator, type_check_def, assert_def, update_pending_deletions_def]
  |> cv_auto_trans;

val () = cv_auto_trans ext_call_kwarg_def;

val () = cv_auto_trans raw_call_value_def;

val () = cv_auto_trans ext_call_opts_ok_def;

val () = eval_ext_call_effects_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, COND_RATOR,
            prod_CASE_rator, sum_CASE_rator, option_CASE_rator, UNCURRY,
            lift_option_def, check_def, assert_def]
  |> cv_auto_trans;

val () = eval_ext_call_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, COND_RATOR,
            prod_CASE_rator, sum_CASE_rator, option_CASE_rator, UNCURRY,
            lift_option_def, lift_option_type_def, type_check_def, check_def,
            assert_def]
  |> cv_auto_trans;

val () = eval_send_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR, COND_RATOR,
            prod_CASE_rator, sum_CASE_rator, option_CASE_rator, UNCURRY,
            lift_option_type_def, type_check_def, check_def, assert_def]
  |> cv_auto_trans;

val () = acquire_nonreentrant_lock_def
  |> SRULE [vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
            FUN_EQ_THM, LET_THM, COND_RATOR,
            get_transient_storage_def, update_transient_def,
            vyperStateTheory.return_def, vyperStateTheory.raise_def]
  |> cv_auto_trans;

val () = release_nonreentrant_lock_def
  |> SRULE [vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
            FUN_EQ_THM, LET_THM,
            get_transient_storage_def, update_transient_def,
            vyperStateTheory.return_def]
  |> cv_auto_trans;

val () = cv_auto_trans next_gas_reading_def;

val () = cv_auto_trans precompile_builtin_def;

val () = cv_auto_trans precompile_call_success_def;

val () = cv_auto_trans code_slice_source_def;

val () = cv_auto_trans is_view_mut_def;

val () = lock_if_nr_def
  |> SRULE [FUN_EQ_THM, COND_RATOR, option_CASE_rator, ignore_bind_def,
            bind_def]
  |> cv_auto_trans;

val () = unlock_if_nr_def
  |> SRULE [FUN_EQ_THM, COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

val () = array_iterator_results_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, LET_RATOR,
            eval_result_CASE_rator, place_CASE_rator, type_value_CASE_rator,
            bound_CASE_rator]
  |> cv_auto_trans;

val () = cv_auto_trans initial_immutables_module_def;

val () = cv_auto_trans initial_immutables_def;

val () = cv_auto_trans lookup_nonreentrant_slot_def;

val () = cv_auto_trans initial_evaluation_context_def;

val () = cv_auto_trans initial_state_def;

val () = cv_auto_trans abstract_machine_from_state_def;

val () = cv_auto_trans merge_constants_def;

val () = cv_auto_trans set_current_module_def;

val () = cv_auto_trans constants_order_def;

val () = send_call_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR]
  |> cv_auto_trans;

val () = cv_auto_trans call_external_raw_return_def;

val () = cv_auto_trans finalize_pending_deletions_def;
