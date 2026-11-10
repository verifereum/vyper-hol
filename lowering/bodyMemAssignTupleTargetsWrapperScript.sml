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
Theorem tuple_targets_source_action:
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
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `su`, `op`, `s0`] mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end r. _` strip_assume_tac >> gvs[]
      >- suspend "normal"
      >> suspend "exception") >>
  suspend "exempt"
QED

Resume compile_assign_tuple_targets_stmt_frag_mem[normal]:
  `!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v, es_end with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  `value_has_type (TupleTV tvs) v` by
    (qpat_x_assum `!obs v es1. _` irule >>
     qexistsl_tac [`es_end with gas_obs := []`,
       `gas_explicit marks s0.vs_gas_readings`] >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout (es_end with gas_obs := []).scopes
      (EL i gs) (EL i tys) (EL i tvs)
      (EL i (case v of ArrayV (TupleV vs) => vs | _ => []))` by
    (drule_all tuple_type_value >> strip_tac >> gvs[] >>
     rpt strip_tac >> simp[] >>
     qpat_x_assum `!obs vs es1 i. _` irule >> simp[] >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings ++ es_end.gas_obs` >>
     first_x_assum (qspec_then `es_end.gas_obs` mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `return_buf_frame d cenv su t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  drule assign_tuple_targets_suffix_mem >>
  simp[] >>
  disch_then (drule_at (Pat `compile_tuple_store_all _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`lctx`, `flag`, `d`] mp_tac) >>
  (impl_tac >- (fs[])) >> strip_tac >>
  qexistsl_tac [`INL ()`, `ee'`, `OK t'`] >> conj_tac
  >- (pure_rewrite_tac [tuple_targets_source_action] >>
      irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
        |> REWRITE_RULE [APPEND_NIL]) >>
      qexistsl_tac [`es_end with gas_obs := []`, `t`, `v`] >> simp[] >>
      conj_tac
      >- (irule gas_marked_exec_end_gas_obs >> simp[]) >>
      simp[gas_marked_exec_def, gas_marked_path_def,
           gas_explicit_def, gas_prefix_def]) >>
  disj1_tac >> simp[] >>
  fs[stmt_post_def] >>
  decide_tac
QED
Resume compile_assign_tuple_targets_stmt_frag_mem[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (pure_rewrite_tac [tuple_targets_source_action] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED
Resume compile_assign_tuple_targets_stmt_frag_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac [tuple_targets_source_action] >>
  ONCE_REWRITE_TAC [ignore_bind_bind_value] >>
  irule gas_exempt_cert_error_value >> simp[]
QED
Finalise compile_assign_tuple_targets_stmt_frag_mem
