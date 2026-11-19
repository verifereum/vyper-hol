Theory vyperSmallStepCV
Ancestors
  arithmetic combin pair list While
  vyperMisc vyperNsidFmap vyperValue vyperContext vyperState vyperCreate vyperInterpreter vyperABI
  vyperCallOutcome[ignore_grammar]
  vyperSmallStep vyperInterpreterCV constSubstCV
Libs
  cv_transLib wordsLib

val liftk1 = oneline liftk_def;

val () = cv_auto_trans no_recursion_def;

val () = eval_base_place_cps_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

val () = cv_auto_trans eval_target_place_cps_def;

val () = cv_auto_trans blueprint_literal_offset_def;

val eval_expr_cps_pre_def = eval_expr_cps_def
   |> SRULE
        [liftk1, bind_def, ignore_bind_def,
         LET_RATOR, option_CASE_rator,
         sum_CASE_rator, prod_CASE_rator, lift_option_def]
   |> cv_auto_trans_pre "eval_expr_cps_pre eval_exprs_cps_pre";

Theorem eval_expr_cps_pre[cv_pre]:
  (∀a b c d. eval_expr_cps_pre a b c d) ∧
  (∀x y z w. eval_exprs_cps_pre x y z w)
Proof
  ho_match_mp_tac eval_expr_cps_ind \\ rw[]
  \\ rw[Once eval_expr_cps_pre_def]
  \\ gvs[CaseEq"prod", CaseEq"sum", CaseEq"option", raise_def, check_def, type_check_def,
         assert_def, builtin_args_length_ok_def, LENGTH_EQ_NUM_compute]
  \\ first_x_assum irule
  \\ gvs[bind_def, ignore_bind_def, lift_option_def, lift_option_type_def, assert_def]
QED

val () = cv_auto_trans eval_iterator_cps_def;

val () = cv_auto_trans assign_tuple_targets_cps_def;

val () = cv_auto_trans eval_stmt_cps_def;

val () = cv_auto_trans eval_stmts_cps_def;

val () = cv_auto_trans eval_for_cps_def;

val () = apply_def
  |> SRULE [liftk1, ignore_bind_def, bind_def, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

val () = apply_exc_def
  |> SRULE [finally_unless_halt_def, finally_def, bind_def, ignore_bind_def,
            liftk1, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

val () = apply_place_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

val () = apply_tv_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

val () = apply_val_range2_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            LET_RATOR, lift_sum_def, bind_def, ignore_bind_def]
  |> cv_auto_trans;

val () = apply_val_subscript_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

val () = apply_val_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, lift_option_def, lift_option_type_def, lift_sum_def, lift_sum_runtime_def,
            LET_RATOR, bind_def, ignore_bind_def]
  |> cv_auto_trans;

Triviality LET4_UNCURRY:
  (let (x,y,z,w) = M in N x y z w) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; w = SND p in N x y z w
Proof
  rw[UNCURRY]
QED

Triviality LET5_UNCURRY:
  (let (x,y,z,w,v) = M in N x y z w v) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; p = SND p; w = FST p; v = SND p in N x y z w v
Proof
  rw[UNCURRY]
QED

Triviality LET6_UNCURRY:
  (let (x,y,z,w,v,u) = M in N x y z w v u) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; p = SND p; w = FST p; p = SND p;
         v = FST p; u = SND p in N x y z w v u
Proof
  rw[UNCURRY]
QED

val apply_vals_pre_def = apply_vals_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, lift_option_def, lift_option_type_def,
             lift_sum_def, lift_sum_runtime_def, prod_CASE_rator, LET_RATOR,
             LET4_UNCURRY, LET5_UNCURRY, LET6_UNCURRY,
            UNCURRY, sum_CASE_rator, option_CASE_rator, COND_RATOR]
  |> cv_auto_trans_pre "apply_vals_pre";

val APPLY_VALS_PRE_CASE_TAC =
  simp[Once apply_vals_pre_def] >>
  gvs[check_def, type_check_def, assert_def] >>
  strip_tac >> gvs[];

Theorem apply_vals_pre[cv_pre]:
  ∀a b c d. apply_vals_pre a b c d
Proof
  ho_match_mp_tac apply_vals_ind \\ rw[] >>
  TRY APPLY_VALS_PRE_CASE_TAC >>
  gvs[check_create_blueprint_state, CaseEq"prod", CaseEq"sum"] >>
  TRY (Cases_on `vs` >> simp[]) >>
  rpt strip_tac >> gvs[optionTheory.IS_SOME_DEF, CaseEq "option", return_def, raise_def]
QED

val () = cv_auto_trans nextk_def;

val () = apply_results_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

val () = cv_auto_trans stepk_def;

val () = cv_trans fromk_def;

val cont_tr_pre_def = cv_trans_pre "cont_pre" cont_tr;

Theorem cont_pre_IS_SOME_cont:
  cont_pre ak ⇔ IS_SOME (cont ak)
Proof
  EQ_TAC
  >- (
    qid_spec_tac`ak`
    \\ ho_match_mp_tac (theorem "cont_pre_ind")
    \\ rw[cont_def, OWHILE_def] \\ gs[]
    >- (
      first_x_assum(qspec_then`SUC n`mp_tac)
      \\ rw[FUNPOW] )
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[] )
  \\ rw[IS_SOME_cont]
  \\ pop_assum mp_tac
  \\ qid_spec_tac`ak`
  \\ Induct_on`n` \\ rw[]
  >- rw[cont_tr_pre_def]
  \\ rw[Once cont_tr_pre_def]
  \\ first_x_assum irule
  \\ gs[FUNPOW]
QED

val () = cv_auto_trans fromtvk_def;

val constants_env_trace_pre_def = constants_env_trace_def
  |> SRULE [bind_def, eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "constants_env_trace_pre";

Theorem constants_env_trace_pre[cv_pre]:
  !cx am addr src ts acc. constants_env_trace_pre cx am addr src ts acc
Proof
  ho_match_mp_tac constants_env_trace_ind
  \\ rw[]
  \\ rw[Once constants_env_trace_pre_def]
  \\ gs[bind_def, eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_rename_tac`eval_expr_cps ec ee es DoneK`
  \\ qspecl_then[`ec`,`ee`,`es`,`DoneK`]mp_tac $ cj 5 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM]
QED

val () = cv_auto_trans constants_env_def;

val () = cv_auto_trans fromvalsk_def;

Theorem cont_pre_eval_exprs_cps[cv_pre]:
  cont_pre (eval_exprs_cps cx es st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont] >>
  qspecl_then [`cx`,`es`,`st`,`DoneK`] mp_tac (cj 6 eval_cps_eq) >>
  rw[cont_def] >> CASE_TAC >> CASE_TAC >> gvs[] >>
  rw[Once OWHILE_THM]
QED

Theorem cont_pre_eval_stmts_cps[cv_pre]:
  cont_pre (eval_stmts_cps cx ss st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont] >>
  qspecl_then [`cx`,`ss`,`st`,`DoneK`] mp_tac (cj 2 eval_cps_eq) >>
  rw[cont_def] >> CASE_TAC >> CASE_TAC >> gvs[] >>
  rw[Once OWHILE_THM]
QED

val evaluate_module_constants_trace_pre_def =
  cv_auto_trans_pre "evaluate_module_constants_trace_pre"
    evaluate_module_constants_trace_def;

Theorem evaluate_module_constants_trace_pre[cv_pre]:
  !cx am addr mods. evaluate_module_constants_trace_pre cx am addr mods
Proof
  ho_match_mp_tac evaluate_module_constants_trace_ind
  \\ rw[]
  \\ rw[Once evaluate_module_constants_trace_pre_def]
QED

val () = cv_auto_trans evaluate_all_constants_def;

val () = call_external_function_trace_def
     |> SRULE [lock_if_nr_def, unlock_if_nr_def, eval_external_defaults_run, eval_exprs_eq_cont_cps,
               eval_stmts_eq_cont_cps, set_scopes_def,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, COND_RATOR, option_CASE_rator,
               get_transient_storage_def, update_transient_def]
     |> cv_auto_trans;

val () = cv_auto_trans call_external_function_def;

val () = cv_auto_trans call_external_def;

val () = cv_auto_trans clear_machine_logs_def;

val () = cv_auto_trans call_external_transaction_def;

val () = cv_auto_trans load_contract_def;

Theorem cont_pre_eval_expr_cps[cv_pre]:
  cont_pre (eval_expr_cps cx e st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont]
  \\ qspecl_then[`cx`,`e`,`st`,`DoneK`]mp_tac $ cj 5 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM]
QED
