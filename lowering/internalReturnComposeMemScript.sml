(* Counted expression evaluation followed by an internal return suffix. *)
Theory internalReturnComposeMem
Ancestors
  stmtSimDefs exprSimMemDefs stmtSimReturn returnValueTyped
  gasSummary gasSummaryCompose gasContext fragGasMode fragGasPathMem fragGasPath
  exprSimDefs exprSimProps stmtSimProps stmtLoweringMono exprLoweringProps
  fragExec gasOutcome
  vyperInterpreter vyperState venomState

Theorem internal_return_value_summary_mem:
  gas_summary_at T (ctx,func) marks
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. expr_exit res r) /\
  (!ee v t. P v ee t /\
    (?gs ee'. bind (eval_expr cx e) (read_result cx)
                (es with gas_obs := gs) = (INL v, ee')) /\ ~t.vs_halted ==>
    ?n r. gas_path_mem ctx func t n r /\ exit_result r /\
      !tail. RetQ v ((ee with gas_obs := tail) with scopes := []) r) ==>
  !Q. ?marks'. gas_summary_at T (ctx,func) marks'
    (eval_stmt cx (Return (SOME e))) (es,s0) Q
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >> gen_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `~t.vs_halted` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >>
         metis_tac[gas_marked_path_exec, gas_path_normal]) >>
      drule marked_exec_source_eq >> strip_tac >>
      first_x_assum drule >> simp[] >>
      (impl_tac >- metis_tac[]) >> strip_tac >>
      qexists_tac `marks ++ REPLICATE n F` >>
      qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
      reverse conj_tac
      >- (simp[stmt_exit_def] >> metis_tac[]) >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `v`] >>
      simp[gas_marked_exec_def, gas_marked_path_def, raise_def]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
  qexists_tac `marks` >> qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Theorem internal_return_value_counted_mem:
  expr_sim_mem ctx func cenv cx ty e es /\
  (!sa sb cenv'' op s1.
    stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
    lower_value compile_expr cenv ty e sa = (op,s1) ==> cs_extends s1 sb) /\
  (!sa sb cenv'' s0 op s1 ee v t.
    stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'',sb) /\
    lower_value compile_expr cenv ty e sa = (op,s1) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    (?gs ee'. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gs) = (INL v,ee')) /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted ==>
    ?n r. gas_path_mem ctx func t n r /\ exit_result r /\
      !tail. RetQ v ((ee with gas_obs := tail) with scopes := []) r) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op,s1)` >>
  `cs_extends s1 sb` by metis_tac[] >>
  `cs_extends sa s1` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`,`s1`,`op`,`s0`] mp_tac) >>
  (impl_tac >- fs[]) >>
  simp[gas_outcome_def] >> strip_tac
  >- (qmatch_goalsub_abbrev_tac `gas_summary_at _ _ _ _ _ Q R` >>
      `?ms. gas_summary_at T (ctx,func) ms
        (eval_stmt cx (Return (SOME e))) (es,s0) Q R` suffices_by metis_tac[] >>
      unabbrev_all_tac >> irule internal_return_value_summary_mem >>
      qexists_tac `\v ee t. expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
        expr_store_bound cx (expr_type e) v op t /\
        t.vs_current_bb = s1.cs_current_bb /\
        t.vs_inst_idx = LENGTH s1.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
      qexists_tac `marks` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[return_forced_exempt]
QED

Theorem internal_return_none_counted_mem:
  (!sa sb s0 cenv''.
    stmt_env cenv lctx ty (Return NONE) sa = (cenv'',sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
    ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?n r. gas_path_mem ctx func s0 n r /\ exit_result r /\
      !tail. RetQ NoneV ((es with gas_obs := tail) with scopes := []) r) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Return NONE)) (eval_stmt cx (Return NONE)) es
Proof
  rw[stmt_frag_mem_def] >>
  first_x_assum (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `s0` mp_tac) >> simp[] >> strip_tac >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `REPLICATE n F` >>
  disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `r`] >>
  simp[Once evaluate_def, raise_def, stmt_exit_def]
QED
