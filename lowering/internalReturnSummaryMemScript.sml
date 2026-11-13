(* Exact terminal predicates for memory-counted internal returns. *)
Theory internalReturnSummaryMem
Ancestors
  bodyMemoryDefs stmtSimDefs stmtSimReturn exprSimMemDefs gasSummaryCompose gasSummary
  gasOutcome gasContext fragGasPathMem fragGasPath fragGasMode exprLoweringProps
  returnValueTyped exprSimDefs
  stmtSimProps stmtLoweringMono loweringPosts vyperInterpreter vyperState
  list fragExec compileEnv
  gasStorage vyperStorageTrace vyperStorageFootprint

(* An exiting counted path's result is its run's: so two exiting counted
   paths from one state end in the same result. *)
Theorem gas_path_mem_exit_run[local]:
  gas_path_mem ctx func s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx func s = r
Proof
  strip_tac >> drule gas_path_mem_exec >> strip_tac >>
  TRY (gvs[exit_result_def] >> NO_TAC) >> metis_tac[]
QED

Theorem gas_path_mem_exit_unique[local]:
  gas_path_mem ctx func s n r /\ gas_path_mem ctx func s n' r' /\
  exit_result r /\ exit_result r' ==> r' = r
Proof
  strip_tac >>
  `?f. run_from f ctx func s = r` by metis_tac[gas_path_mem_exit_run] >>
  `?f'. run_from f' ctx func s = r'` by metis_tac[gas_path_mem_exit_run] >>
  `run_from (f + f') ctx func s = r` by
    (irule gas_run_from_fuel_mono >>
     conj_tac >- metis_tac[exit_result_not_error] >>
     qexists_tac `f` >> simp[]) >>
  `run_from (f + f') ctx func s = r'` by
    (irule gas_run_from_fuel_mono >>
     conj_tac >- metis_tac[exit_result_not_error] >>
     qexists_tac `f'` >> simp[]) >>
  metis_tac[]
QED

(* Per-horizon exiting paths from one state give one path for every
   horizon. *)
Theorem path_uniform_retq[local]:
  !Q V H0 ctx func t.
    (!H r. Q H r ==> exit_result r) /\ V H0 /\
    (!H. V H ==> ?n r. gas_path_mem ctx func t n r /\ Q H r) ==>
    ?n r. gas_path_mem ctx func t n r /\ !H. V H ==> Q H r
Proof
  rpt strip_tac >>
  qpat_assum `!H. V H ==> _` (qspec_then `H0` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qexistsl_tac [`n`, `r`] >> simp[] >> rpt strip_tac >>
  qpat_x_assum `!H. V H ==> _` (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `r' = r` suffices_by (strip_tac >> gvs[]) >>
  irule gas_path_mem_exit_unique >> metis_tac[]
QED

Theorem internal_return_none_summary_mem:
  (!H v ee r. RetQ H v ee r ==> exit_result r) /\
  (!H v ee gs r. RetQ H v (ee with gas_obs := gs) r = RetQ H v ee r) /\
  (!H st0 sa sb s0 cenv''.
     valid_horizon cx st0 H es.storage_trace /\
     stmt_env cenv lctx ty (Return NONE) sa = (cenv'', sb) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
     ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
     stmt_state_rel H ctx func cenv cx es s0 /\
     alloca_history func s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
     s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
     ?n r. gas_path_mem ctx func s0 n r /\
           RetQ H NoneV (es with scopes := []) r) ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Return NONE)) (eval_stmt cx (Return NONE)) es
Proof
  rw[stmt_frag_mem_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >>
      simp[evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[storage_trace_domain_def] >>
  qspecl_then [`\H r. RetQ H NoneV (es with scopes := []) r`,
               `\H. valid_horizon cx st0 H es.storage_trace`, `H0`,
               `ctx`, `func`, `s0`] mp_tac path_uniform_retq >>
  BETA_TAC >> impl_tac
  >- (conj_tac >- metis_tac[] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >>
      qpat_x_assum `!H st0 sa sb s0 cenv''. _`
        (qspecl_then [`H`, `st0`, `sa`, `sb`, `s0`, `cenv'`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> disch_then ACCEPT_TAC) >>
  strip_tac >>
  `exit_result r` by metis_tac[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `REPLICATE n F` >>
  disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `r`] >>
  simp[Once evaluate_def, raise_def, stmt_exit_def] >>
  TRY disj2_tac >> rpt strip_tac >> TRY disj2_tac >>
  `RetQ H NoneV (es with scopes := []) r` by metis_tac[] >>
  qpat_x_assum `!H v ee gs r. _`
    (qspecl_then [`H`, `NoneV`, `es with scopes := []`, `tail`, `r`] mp_tac) >>
  simp[]
QED

(* The value ran out of the storage domain: so does the whole return. *)
val ret_bad_tac =
  qexists_tac `marks` >> disj1_tac >>
  irule gas_bad_storage_at_bind_left >>
  simp[storage_trace_frame_raise] >>
  irule gas_bad_storage_at_counted_prefix >> metis_tac[];

Theorem internal_return_summary_bind_mem[local]:
  gas_summary_at T (ctx,func) marks source (es,s0)
    (\res ee t. !H. valid_horizon cx st0 H ee.storage_trace ==> P H res ee t)
    (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_exit res r) /\
  (!H res ee t. P H res ee t ==> ?v. res = INL v) /\
  (!H v ee r. RetQ H v ee r ==> exit_result r) /\
  (!H v ee gs r. RetQ H v (ee with gas_obs := gs) r = RetQ H v ee r) /\
  (!H ee v t.
     valid_horizon cx st0 H ee.storage_trace /\ P H (INL v) ee t /\
     (?gs. source (es with gas_obs := gs) = (INL v, ee with gas_obs := [])) /\
     ~t.vs_halted ==>
     ?n r. gas_path_mem ctx func t n r /\
           RetQ H v (ee with scopes := []) r) ==>
  !Q. ?marks'.
    gas_bad_storage_at cx st0
      (bind source (\v. (raise (ReturnException v) :
         evaluation_state -> (unit + exception) # evaluation_state)))
      es s0 marks' \/
    gas_summary_at T (ctx,func) marks'
      (bind source (\v. (raise (ReturnException v) :
         evaluation_state -> (unit + exception) # evaluation_state))) (es,s0) Q
      (\res ee r. !H. valid_horizon cx st0 H ee.storage_trace ==>
         !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  strip_tac >> gen_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`
      >- (`?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
            metis_tac[storage_trace_domain_def] >>
          `?v. res = INL v` by
            (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
               (qspec_then `H0` mp_tac) >> simp[] >> metis_tac[]) >>
          gvs[] >>
          `~t.vs_halted` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >>
             metis_tac[gas_marked_path_exec, gas_path_normal]) >>
          `?gs. source (es with gas_obs := gs) =
                  (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >> metis_tac[]) >>
          qspecl_then
            [`\H r. RetQ H v ((es_end with gas_obs := []) with scopes := []) r`,
             `\H. valid_horizon cx st0 H es_end.storage_trace`, `H0`,
             `ctx`, `func`, `t`] mp_tac path_uniform_retq >>
          BETA_TAC >> impl_tac
          >- (conj_tac >- metis_tac[] >> conj_tac >- first_assum ACCEPT_TAC >>
              rpt strip_tac >>
              qpat_x_assum `!H ee v t. _ ==> ?n r. _` irule >>
              simp[] >> metis_tac[]) >>
          strip_tac >> qexists_tac `marks ++ REPLICATE n F` >> disj2_tac >>
          qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
          `exit_result r` by metis_tac[] >>
          conj_tac
          >- (irule gas_marked_exec_bind_normal >>
              qexistsl_tac [`es_end`, `t`, `v`] >>
              simp[gas_marked_exec_def, gas_marked_path_def, raise_def]) >>
          simp[stmt_exit_def] >>
          TRY disj2_tac >> rpt strip_tac >> TRY disj2_tac >>
          `RetQ H v (es_end with scopes := []) r` by
            (`RetQ H v ((es_end with scopes := []) with gas_obs := []) r` by
               (qpat_assum `!H. valid_horizon _ _ H _ ==> RetQ _ _ _ _`
                  (qspec_then `H` mp_tac) >>
                impl_tac >- first_assum ACCEPT_TAC >>
                simp_tac (srw_ss()) []) >>
             metis_tac[]) >>
          qpat_x_assum `!H v ee gs r. _`
            (qspecl_then [`H`, `v`, `es_end with scopes := []`, `tail`, `r`]
               mp_tac) >>
          simp[]) >>
      ret_bad_tac) >>
  Cases_on `storage_trace_domain cx st0 es_end.storage_trace`
  >- (`?H0. valid_horizon cx st0 H0 es_end.storage_trace` by
        metis_tac[storage_trace_domain_def] >>
      `?ex. res = INR ex` by
        (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
           (qspec_then `H0` mp_tac) >>
         impl_tac >- gs[] >> strip_tac >>
         Cases_on `res` >> gvs[expr_exit_def]) >>
      gvs[] >>
      qexists_tac `marks` >> disj2_tac >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  ret_bad_tac
QED

Theorem internal_return_value_counted_mem:
  (!H v ee r. RetQ H v ee r ==> exit_result r) /\
  (!H v ee gs r. RetQ H v (ee with gas_obs := gs) r = RetQ H v ee r) /\
  (!ty'. expr_sim_mem ctx func cenv cx ty' e es /\
         expr_vv_sim_mem ctx func cenv cx ty' e es) /\
  (!sa sb cenv'' op s1.
     stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'', sb) /\
     lower_value compile_expr cenv ty e sa = (op, s1) ==> cs_extends s1 sb) /\
  (!H st0 sa sb cenv'' s0 op s1 ee v t.
     valid_horizon cx st0 H ee.storage_trace /\
     stmt_env cenv lctx ty (Return (SOME e)) sa = (cenv'', sb) /\
     lower_value compile_expr cenv ty e sa = (op, s1) /\
     fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
     local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
     ~block_is_terminated sa /\ return_buf_frame d cenv sa s0 /\
     (!H'. valid_horizon cx st0 H' es.storage_trace ==>
           stmt_state_rel H' ctx func cenv cx es s0) /\
     alloca_history func s0 /\
     ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
     s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
     expr_post H ctx func cenv cx e es sa s1 s0 ee v op t /\
     expr_store_bound cx (expr_type e) v op t /\
     (?gs. bind (eval_expr cx e) (read_result cx)
                 (es with gas_obs := gs) = (INL v, ee with gas_obs := [])) /\
     t.vs_current_bb = s1.cs_current_bb /\
     t.vs_inst_idx = LENGTH s1.cs_current_insts /\
     alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
     ~t.vs_halted /\ return_buf_frame d cenv s1 t ==>
     ?n r. gas_path_mem ctx func t n r /\
           RetQ H v (ee with scopes := []) r) ==>
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
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `op`, `s0`] mp_tac) >>
  impl_tac >- fs[] >> simp[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> asm_rewrite_tac[] >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_raise])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o HO_MATCH_MP
           (REWRITE_RULE [GSYM AND_IMP_INTRO] internal_return_summary_bind_mem)) >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      impl_tac >- first_assum ACCEPT_TAC >>
      impl_tac
      >- (rpt gen_tac >> BETA_TAC >> rpt strip_tac >> gvs[] >>
          `return_buf_frame d cenv s1 t` by
            (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
             qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
             rewrite_tac[expr_post_def] >> strip_tac >> simp[]) >>
          qpat_x_assum `!H st0 sa sb cenv'' s0 op s1 ee v t. _`
            (qspecl_then [`H`, `st0`, `sa`, `sb`, `cenv'`, `s0`, `op`, `s1`,
                          `ee`, `v`, `t`] mp_tac) >>
          impl_tac >- (simp[] >> metis_tac[]) >> disch_then ACCEPT_TAC) >>
      strip_tac >> asm_rewrite_tac[] >>
      qmatch_goalsub_abbrev_tac `gas_summary_at T _ _ _ _ QQ _ \/ _` >>
      qpat_x_assum `!Q. _` (fn th =>
        Q_TAC (fn qq => strip_assume_tac (ISPEC qq th)) `QQ`) >>
      qexists_tac `marks'` >>
      asm_rewrite_tac[]) >>
  drule (GEN_ALL return_forced_exempt) >> asm_rewrite_tac[] >> strip_tac >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >> goal_assum (drule_at Any)
QED
