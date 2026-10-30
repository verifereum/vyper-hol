(* TOP-LEVEL: construct the argument-list compiler plan from actual code,
   evaluated layout sizes and expression compiler structure. Snapshot
   requests come from the emitted instruction profile, not a callback. *)
Theory logArgumentPlan
Ancestors
  logArgumentListContract logArgumentCode logArgumentSnapshotRequests logArgumentIdFlow
  compileAllocationRequests compileAllocaProvenance compileIdFlow compileAppendProps
  compileVyper vyperTypeContract exprLowering stmtLowering context compileEnv
  fragExec list pair words

Theorem compile_log_eval_all_cons_context:
  !cenv e suffix cs ops cut final_cut func.
    EVERY (\arg. cs_appends (lower_value compile_expr cenv (expr_type arg) arg)) (e::suffix) /\
    compile_log_eval_all cenv (e::suffix) cs = (ops,cut) /\
    cs_extends cut final_cut /\ fn_has_code cs final_cut func ==>
    ?src load_cut saved save_cut rest.
      lower_value compile_expr cenv (expr_type e) e cs = (src,load_cut) /\
      compile_log_save_arg cenv (lowered_value_type cenv e) src suffix load_cut = (saved,save_cut) /\
      compile_log_eval_all cenv suffix save_cut = (rest,cut) /\ ops = (saved,lowered_value_type cenv e)::rest /\
      cs_extends cs load_cut /\ cs_extends load_cut save_cut /\ cs_extends save_cut cut /\
      cs_extends cs save_cut /\ cs_extends save_cut final_cut /\
      fn_has_code cs load_cut func /\ fn_has_code load_cut save_cut func /\ fn_has_code save_cut final_cut func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends cs cut` by
    (qspecl_then [`compile_log_eval_all cenv (e::suffix)`, `cs`, `ops`, `cut`]
      mp_tac cs_appends_result_extends >> simp[cs_appends_compile_log_eval_all]) >>
  `fn_has_code cs cut func` by
    (qspecl_then [`cs`, `cut`, `final_cut`, `func`] mp_tac fn_has_code_split >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qspecl_then [`cenv`, `e`, `suffix`, `cs`, `ops`, `cut`, `func`] mp_tac compile_log_eval_all_cons_contains >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `src` (qx_choose_then `load_cut` (qx_choose_then `saved`
    (qx_choose_then `save_cut` (qx_choose_then `rest` strip_assume_tac))))) >>
  `cs_extends cs save_cut` by (irule cs_extends_trans >> qexists_tac `load_cut` >> simp[]) >>
  `cs_extends save_cut final_cut` by (irule cs_extends_trans >> qexists_tac `cut` >> simp[]) >>
  `fn_has_code save_cut final_cut func` by
    (qspecl_then [`cs`, `save_cut`, `final_cut`, `func`] mp_tac fn_has_code_split >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  qexistsl_tac [`src`, `load_cut`, `saved`, `save_cut`, `rest`] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_log_eval_all_plan:
  !args tvs tops cenv func profile_start cs ops cut final_cut.
    struct_args_unique tops /\ cenv.ce_struct_fields = make_struct_fields_map tops /\
    EVERY (\e. cs_appends (lower_value compile_expr cenv (expr_type e) e)) args /\
    EVERY (\e. compiler_id_flow (lower_value compile_expr cenv (expr_type e) e)) args /\
    LIST_REL (\e tv. evaluate_type (type_env tops) (lowered_value_type cenv e) = SOME tv /\
      type_memory_size tv < dimword(:256)) args tvs /\
    compiler_id_history cs /\ cs_extends profile_start cs /\
    compile_log_eval_all cenv args cs = (ops,cut) /\ cs_extends cut final_cut /\ fn_has_code cs final_cut func ==>
    log_argument_plan tops cenv func (compiler_alloca_ids profile_start final_cut)
      (compiler_alloca_requests profile_start final_cut) final_cut args cs cut
Proof
  Induct_on `args`
  >- (rpt gen_tac >> simp[Once compile_log_eval_all_def, comp_return_def, log_argument_plan_def]) >>
  rpt gen_tac >> Cases_on `tvs` >- simp[] >>
  rename1 `LIST_REL _ (e::suffix) (tv::rest_tvs)` >>
  simp_tac bool_ss [EVERY_DEF, LIST_REL_def] >> strip_tac >>
  qspecl_then [`cenv`, `e`, `suffix`, `cs`, `ops`, `cut`, `final_cut`, `func`]
    mp_tac compile_log_eval_all_cons_context >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC, simp[]]) >>
  disch_then (qx_choose_then `src` (qx_choose_then `load_cut` (qx_choose_then `saved`
    (qx_choose_then `save_cut` (qx_choose_then `rest` strip_assume_tac))))) >>
  `compiler_id_history load_cut` by
    (qspecl_then [`lower_value compile_expr cenv (expr_type e) e`, `cs`, `src`, `load_cut`]
      mp_tac compiler_id_flow_result >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `compiler_id_history save_cut` by
    (qspecl_then [`cenv`, `lowered_value_type cenv e`, `src`, `suffix`, `load_cut`, `saved`, `save_cut`]
      mp_tac compile_log_save_arg_id_history >> simp[]) >>
  `cs_extends profile_start load_cut` by (irule cs_extends_trans >> qexists_tac `cs` >> simp[]) >>
  `cs_extends profile_start save_cut` by (irule cs_extends_trans >> qexists_tac `cs` >> simp[]) >>
  `cs_extends load_cut final_cut` by (irule cs_extends_trans >> qexists_tac `save_cut` >> simp[]) >>
  `!request. MEM request (compiler_alloca_requests cs load_cut) ==>
    MEM request (compiler_alloca_requests profile_start final_cut)` by
    (qspecl_then [`profile_start`, `cs`, `load_cut`, `final_cut`] mp_tac compiler_alloca_requests_subprofile >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp_tac bool_ss []) >>
  `~is_word_type (lowered_value_type cenv e) /\ ~EVERY pure_expr suffix ==>
    MEM (load_cut.cs_next_id,type_memory_size tv) (compiler_alloca_requests profile_start final_cut) /\
    MEM load_cut.cs_next_id (compiler_alloca_ids profile_start final_cut)` by
    (strip_tac >> qspecl_then [`tops`, `cenv`, `lowered_value_type cenv e`, `src`, `suffix`, `load_cut`,
       `saved`, `save_cut`, `profile_start`, `final_cut`, `tv`] mp_tac compile_log_save_arg_profile_request >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `log_argument_plan tops cenv func (compiler_alloca_ids profile_start final_cut)
    (compiler_alloca_requests profile_start final_cut) final_cut suffix save_cut cut` by
    (qpat_x_assum `!tvs tops cenv func profile_start cs ops cut final_cut. _`
       (qspecl_then [`rest_tvs`, `tops`, `cenv`, `func`, `profile_start`, `save_cut`, `rest`, `cut`, `final_cut`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  simp_tac bool_ss [Once log_argument_plan_def] >>
  qexistsl_tac [`src`, `load_cut`, `saved`, `save_cut`, `tv`] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
