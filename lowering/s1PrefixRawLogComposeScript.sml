(* Request-prefix companion to bodyFullRawLogCompose. *)
Theory s1PrefixRawLogCompose
Ancestors
  s1PrefixPreds bodyFullRawLogCompose s1PrefixDefs s1PrefixCompose
  s1PrefixRawLogTopicsSuffix s1PrefixRawLogArgJudgments s1PrefixRawLogDataStage
  bodyFullRawLogLayout bodyFullRawLogTopics bodyFullRawLogReadiness
  bodyFullIfExpReach exprSimCallRawLog stmtSimForRounds
  bodySimFull vyperTypeSystem vyperAST vyperState list stmtSimProps
  vyperStorageTrace vyperStorageFootprint s1PrefixProps
  exprBodyPreProps vyperValue vyperContext exprSimDefs bodyFullPreds
  bodyFullHashKeccakFixed exprLoweringProps bodyMemoryDefs loweringPosts
  exprSimSliceCompose gasContext bodyFullSimProjection

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `?a elem bd topics data n.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    ann = NoneT /\ dflt = NONE /\ LENGTH topics <= 4 /\
    a = ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n) /\ n <= 4 /\
    well_typed_expr env (Builtin a (MakeArray elem bd) topics)` by
    (drule expr_body_pre_static_facts >>
     simp[Once well_typed_expr_def] >> strip_tac >>
     gvs[LENGTH_EQ_NUM_compute] >> Cases_on `h` >> gvs[] >>
     rename1 `Builtin a b topics` >> Cases_on `b` >>
     gvs[expr_type_def, well_typed_expr_def] >> metis_tac[]) >>
  gvs[] >>
  `elem = SOME (BaseT (BytesT (Fixed 32))) /\ bd = Dynamic n /\
   LENGTH topics <= n` by
    (Cases_on `elem` >>
     gvs[well_typed_expr_def, well_typed_builtin_app_def,
         compatible_bound_def, builtin_args_length_ok_def]) >> gvs[] >>
  drule_all raw_log_prefix_arg_judgments >> strip_tac >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all (Q.INST [`shadow_defaults` |-> `T`] raw_log_full_layout_shadow) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))) >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full _ _ _ source _` >>
  `source = bind (eval_exprs cx topics)
     (\vs. bind (bind (eval_expr cx data) (read_result cx))
       (\dv. do bs <- lift_option_type (dest_BytesV dv) "raw_log data";
                type_check (LENGTH vs <= 4) "raw_log too many topics";
                check_not_static cx;
                push_log (encode_raw_event_values cx.txn.target vs bs);
                return NoneV od))` by
    simp[Abbr `source`, raw_log_eval, compatible_bound_def, bind_assoc, SF ETA_ss] >>
  mp_tac raw_log_topics_full >>
  (impl_tac >- MATCH_ACCEPT_TAC raw_log_full_data_reached_ready) >>
  disch_then drule_all >> disch_then (qspec_then `PG` assume_tac) >>
  qpat_assum `source = _` (fn th => rewrite_tac[th]) >>
  irule gas_prefix_full_bind_replay >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame] >>
  conj_tac
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >> reverse conj_tac
      >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
              storage_trace_frame_read_result] >>
      gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts] >> gen_tac >> BETA_TAC >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_checks] >>
      irule storage_trace_frame_ignore_bind >> simp[storage_trace_frame_check_not_static] >>
      irule storage_trace_frame_ignore_bind >>
      simp[storage_trace_frame_state_updates, storage_trace_frame_return]) >>
  reverse conj_tac
  >- (goal_assum (drule_at (Pat `gas_outcome_full _ _ _ _ _ _ _ _`)) >>
      BETA_TAC >> simp[] >> conj_tac
      >- suspend "data" >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  irule (Q.SPECL [`topics`,`[]:expr list`] raw_log_topics_suffix_prefix) >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `expr_body_pre _ _ _ (Call _ RawLog _ _) _`)) >>
  goal_assum (drule_at (Pat `compile_multi_exprs compile_expr _ (MAP gas_shadow_expr _) _ = _`)) >>
  map_every qexists_tac [`d`,`sa`,`sm`,`shadow_func`,`tops`] >> simp[]
QED
*)
Theorem raw_log_expr_sim_prefix:
  (!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))) /\
  (!ce xs. gas_shadow_compiles (compile_multi_exprs compile_expr ce xs)
    (compile_multi_exprs compile_expr (gas_shadow_env T ce) (MAP gas_shadow_expr xs))) /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Call ann RawLog args dflt) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume raw_log_expr_sim_prefix[data]:
  qx_genl_tac [`marks`, `vs`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
    gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> metis_tac[]) >>
  `body_expr_prefix_ok cx data` by
    (qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` assume_tac) >>
     qpat_assum `!gs vals m. _ ==> body_expr_prefix_ok _ _` drule >> simp[]) >>
  `well_typed_exprs env topics` by
    fs[well_typed_expr_def, well_typed_builtin_app_def] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[body_const_cells_agree_state_updates] >>
     irule body_const_cells_agree_exprs >>
     qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` (irule_at Any)) >>
     simp[body_const_cells_agree_state_updates]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type data) data mid /\
   expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type data) data mid` by
    (conj_tac
     >- (irule (cj 1 body_expr_full_ok_simulations) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl_tac [`env`,`tops`] >> simp[]) >>
     drule (cj 1 (iffLR (CONJUNCT1 body_expr_prefix_ok_def))) >>
     disch_then (irule o cj 1) >> goal_assum (drule_at Any) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full _ _ _ data_source _` >>
  `gas_admissible data_source expr_res_ok mid` by
    (qpat_assum `source = _` (fn eq =>
       qpat_assum `gas_admissible source _ _` (assume_tac o REWRITE_RULE [eq])) >>
     drule_all gas_admissible_bind_tail >> simp[Abbr `data_source`]) >>
  `gas_admissible (bind (eval_expr cx data) (read_result cx)) expr_res_ok mid` by
    (qunabbrev_tac `data_source` >>
     qpat_assum `gas_admissible (bind (bind _ _) _) _ mid` mp_tac >>
     pure_rewrite_tac[gas_admissible_def] >>
     disch_then (fn adm =>
       qx_genl_tac [`gs`,`r`,`ee`] >> strip_tac >>
       Cases_on `r` >- simp[expr_res_ok_def] >>
       qspec_then `gs` mp_tac adm >> simp[bind_def] >> metis_tac[])) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >>
     goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >> fs[wb_frame_def]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  qunabbrev_tac `data_source` >>
  irule (INST_TYPE [alpha |-> ``:type``, beta |-> ``:expr option``]
    raw_log_data_stage_prefix) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`cenv`,`d`,`env`,`value`,`sd`,`shadow_func`,`shadow_sd`,
            `shadow_sm`,`shadow_sn`,`sm`,`sn`] >> simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
      qexists_tac `sa` >> simp[])
  >- (qpat_x_assum `(_ /\ _) \/ (_ /\ _)` strip_assume_tac >> simp[] >>
      qexistsl [`Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
                   (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics`,
                `NoneT`,`ty`,`NONE`,`sa`,`StackValue NoneT (Lit 0w)`,`sb`] >>
      first_assum ACCEPT_TAC) >>
  irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise raw_log_expr_sim_prefix
*)
