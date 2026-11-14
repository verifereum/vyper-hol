(* Exact terminal predicates for memory-counted internal returns. *)
Theory internalReturnSummaryMem
Ancestors
  bodyMemoryDefs stmtSimDefs stmtSimReturn exprSimMemDefs gasSummaryCompose gasSummary
  gasOutcome gasContext fragGasPathMem fragGasPath fragGasMode exprLoweringProps
  returnValueTyped exprSimDefs
  stmtSimProps stmtLoweringMono loweringPosts vyperInterpreter vyperState
  list fragExec compileEnv

Theorem internal_return_none_summary_mem:
  (!v ee r. RetQ v ee r ==> exit_result r) /\
  (!v ee gs r. RetQ v (ee with gas_obs := gs) r = RetQ v ee r) /\
  (!sa sb s0 cenv''.
     stmt_env cenv lctx ty (Return NONE) sa = (cenv'', sb) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
     ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
     stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
     s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
     ?n r. gas_path_mem ctx func s0 n r /\
       RetQ NoneV (es with scopes := []) r) ==>
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
  simp[Once evaluate_def, raise_def, stmt_exit_def] >>
  disj2_tac >> conj_tac >- metis_tac[] >>
  gen_tac >> disj2_tac >>
  qpat_x_assum `!v ee gs r. _`
    (qspecl_then [`NoneV`, `es with scopes := []`, `tail`, `r`] mp_tac) >>
  simp[]
QED

Theorem internal_return_summary_bind_mem[local]:
  gas_summary_at T (ctx,func) marks source (es,s0) P
    (\res ee r. expr_exit res r /\ halt_exit cx ee res r) /\
  (!res ee t. P res ee t ==> ?v. res = INL v) /\ 
  (!v ee r. RetQ v ee r ==> exit_result r) /\
  (!v ee gs r. RetQ v (ee with gas_obs := gs) r = RetQ v ee r) /\
  (!ee v t.
     P (INL v) ee t /\
     (?gs. source (es with gas_obs := gs) = (INL v, ee with gas_obs := [])) /\
     ~t.vs_halted ==>
     ?n r. gas_path_mem ctx func t n r /\ RetQ v (ee with scopes := []) r) ==>
  !Q. ?marks'. gas_summary_at T (ctx,func) marks'
    (bind source (\v. raise (ReturnException v))) (es,s0) Q
    (\res ee r. (!tail. stmt_exit RetQ (ee with gas_obs := tail) res r) /\ halt_exit cx ee res r)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
      `~t.vs_halted` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >>
         metis_tac[gas_marked_path_exec, gas_path_normal]) >>
      `?gs. source (es with gas_obs := gs) =
              (INL v, es_end with gas_obs := [])` by
        (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
         simp[gas_marked_exec_def] >> metis_tac[]) >>
      qpat_x_assum `!ee v t. _`
        (qspecl_then [`es_end with gas_obs := []`, `v`, `t`] mp_tac) >>
      simp[] >> impl_tac >- metis_tac[] >>
      strip_tac >> qexists_tac `marks ++ REPLICATE n F` >>
      qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
      conj_tac
      >- (irule gas_marked_exec_bind_normal >>
          qexistsl_tac [`es_end`, `t`, `v`] >>
          simp[gas_marked_exec_def, gas_marked_path_def, raise_def]) >>
      simp[stmt_exit_def] >> disj2_tac >>
      conj_tac >- metis_tac[] >> gen_tac >> disj2_tac >>
      qpat_assum `!v ee gs r. _`
        (qspecl_then [`v`, `es_end with scopes := []`, `tail`, `r`] mp_tac) >>
      qpat_x_assum `!v ee gs r. _`
        (qspecl_then [`v`, `es_end with scopes := []`, `[]`, `r`] mp_tac) >>
      simp[]) >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
  qexists_tac `marks` >> qexistsl_tac [`INR ex`, `es_end`, `r`] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Theorem internal_return_value_counted_mem:
  (!v ee r. RetQ v ee r ==> exit_result r) /\
  (!v ee gs r. RetQ v (ee with gas_obs := gs) r = RetQ v ee r) /\
  (!ty'. expr_sim_mem ctx func cenv cx ty' e es /\
         expr_vv_sim_mem ctx func cenv cx ty' e es) /\
  (!sa sb cenv'' op s1.
     stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'', sb) /\
     lower_value compile_expr cenv ty e sa = (op, s1) ==> cs_extends s1 sb) /\
  (!sa sb cenv'' s0 op s1 ee v t.
     stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'', sb) /\
     lower_value compile_expr cenv ty e sa = (op, s1) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
     ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
     stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
     s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
     expr_post ctx func cenv cx e es sa s1 s0 ee v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     (?gs. bind (eval_expr cx e) (read_result cx)
                 (es with gas_obs := gs) = (INL v, ee with gas_obs := [])) /\
     t.vs_current_bb = s1.cs_current_bb /\
     t.vs_inst_idx = LENGTH s1.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ~t.vs_halted /\ return_buf_frame d cenv s1 t ==>
     ?n r. gas_path_mem ctx func t n r /\ RetQ v (ee with scopes := []) r) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Return (SOME e))) (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lower_value compile_expr cenv ty e sa` >> rename1 `_ = (op, s1)` >>
  `cs_extends s1 sb` by metis_tac[] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa, ci_mono_def, pairTheory.SND] >>
  `fn_has_code sa s1 func` by metis_tac[fn_has_code_split] >>
  `expr_sim_mem ctx func cenv cx ty e es` by fs[] >>
  drule (GEN_ALL return_forced_admissible) >> strip_tac >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- fs[] >> simp[gas_outcome_def] >> strip_tac
  >- (drule internal_return_summary_bind_mem >>
      disch_then (qspec_then `RetQ` mp_tac) >>
      rewrite_tac[RIGHT_FORALL_IMP_THM] >> impl_tac
      >- (simp[] >> conj_tac >- (rpt strip_tac >> metis_tac[]) >>
          conj_tac >- first_assum ACCEPT_TAC >>
          rpt gen_tac >> strip_tac >>
          `return_buf_frame d cenv s1 t` by
            (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
             qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
             simp[expr_post_def] >> strip_tac >> simp[]) >>
          first_x_assum (drule_all o Ho_Rewrite.PURE_REWRITE_RULE [PULL_EXISTS]) >>
          simp[]) >>
      strip_tac >>
      `eval_stmt cx (Return (SOME e)) =
       bind (bind (eval_expr cx e) (read_result cx))
         (\v. raise (ReturnException v))` by
        (simp[FUN_EQ_THM, eval_return_forced] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
      asm_rewrite_tac[] >>
      qpat_x_assum `!Q. _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  drule (GEN_ALL return_forced_exempt) >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> goal_assum (drule_at Any)
QED
