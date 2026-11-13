(* Counted memory wrapper for tuple target assignment. *)
Theory bodyMemAssignTupleTargetsWrapper
Ancestors
  bodyMemAssignTupleTargetsSuffix bodyMemoryDefs exprSimMemDefs
  stmtSimAssignTupleTargets stmtSimForced tupleAssignParts tupleStageProps
  exprLoweringProps exprLowering stmtSimDefs loweringPosts gasOutcome
  gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  vyperInterpreter vyperState list rich_list finite_map compileEnv fragExec
  stmtSimReturn valueEncoding stmtSimDeclCompose gasContext gasOracleReplay
  exprSimDefs stmtSimProps
Libs
  monadsyntax

(* S1 original: stmtSimAssignTuple.eval_assign_tuple_action. *)
Theorem tuple_targets_source_action[local]:
  eval_stmt cx (Assign (TupleTarget gs) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (assign_tuple_targets cx (TupleTarget gs))
Proof
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem compile_assign_tuple_targets_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty gs e es tys tvs.
    expr_type e = TupleT tys /\ LENGTH gs = LENGTH tys /\
    lowered_value_type cenv e = expr_type e /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
    (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
      type_memory_size (TupleTV tvs) < dimword (:256)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs)) /\
    (!i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
      type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
    (!obs v es1. (do result <- eval_expr cx e; read_result cx result od)
      (es with gas_obs := obs) = (INL v,es1) ==>
      value_has_type (TupleTV tvs) v) /\
    (!obs vs es1 i.
      (do result <- eval_expr cx e; read_result cx result od)
        (es with gas_obs := obs) = (INL (ArrayV (TupleV vs)),es1) /\
      i < LENGTH gs ==>
      tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
    gs <> [] /\
    expr_sim_mem ctx func cenv cx (TupleT tys) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_targets_code_parts >> strip_tac >> gvs[] >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su /\ cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >>
     qexistsl_tac [`assign_tuple_targets cx (TupleTarget gs)`, `lctx`] >>
     fs[tuple_targets_source_action]) >>
  pure_rewrite_tac [tuple_targets_source_action] >>
  irule forced_then_outcome >>
  qexists_tac `\H v ee t.
    expr_post H ctx func cenv cx e es sa su s0 ee v op t /\
    expr_store_bound cx (expr_type e) v op t /\
    t.vs_current_bb = su.cs_current_bb /\
    t.vs_inst_idx = LENGTH su.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`expr_exit (INR _) _`]
  >- (rpt strip_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >~ [`gas_outcome _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`st0`, `sa`, `su`, `op`, `s0`] mp_tac) >>
      simp[]) >>
  suspend "tail"
QED

Resume compile_assign_tuple_targets_stmt_frag_mem[tail]:
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  rename1 `valid_horizon cx st0 H1 ee.storage_trace` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post H ctx func cenv cx e es sa su s0 ee v op t` by
    (rpt strip_tac >> metis_tac[]) >>
  `t.vs_current_bb = su.cs_current_bb` by metis_tac[] >>
  `t.vs_inst_idx = LENGTH su.cs_current_insts` by metis_tac[] >>
  `alloca_history func t` by metis_tac[] >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by metis_tac[] >>
  `expr_post H1 ctx func cenv cx e es sa su s0 ee v op t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
       drule >> disch_then ACCEPT_TAC) >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout ee.scopes (EL i gs) (EL i tys) (EL i tvs)
      (EL i (case v of ArrayV (TupleV vs) => vs | _ => []))` by
    (drule_all tuple_type_value >> strip_tac >> gvs[] >> metis_tac[]) >>
  `return_buf_frame d cenv su t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[loweringPostsTheory.post_value_type_lowered] >>
  drule_all (SIMP_RULE bool_ss [PULL_EXISTS] assign_tuple_targets_suffix_mem) >>
  disch_then (qspec_then `lctx` strip_assume_tac) >>
  `s0.vs_alloca_next <= t'.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`INL ()`, `ee'`, `OK t'`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[gas_marked_path_def] >>
  disj1_tac >> qexists_tac `t'` >> simp[] >>
  qx_gen_tac `H'` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee'.storage_trace ==> _` drule >>
  strip_tac >>
  qexists_tac `cenv` >> simp[]
QED

Finalise compile_assign_tuple_targets_stmt_frag_mem
