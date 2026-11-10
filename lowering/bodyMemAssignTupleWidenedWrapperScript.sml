(* Counted composition for an unstaged physical tuple result. *)
Theory bodyMemAssignTupleWidenedWrapper
Ancestors
  bodyMemAssignTupleTargetsWrapper bodyMemAssignTupleWidenedSuffix
  tupleWidenedReadiness tupleWidenedMarkedRead tupleUnstagedParts externalNormalizePremises
  bodyMemoryDefs exprSimMemDefs stmtSimForced exprLoweringProps exprLowering
  stmtSimDefs loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath vyperInterpreter vyperState list
  rich_list finite_map compileEnv fragExec stmtSimReturn valueEncoding
  stmtSimDeclCompose gasContext gasOracleReplay exprSimDefs stmtSimProps
  exprSimHypsDefs typedMemoryCopy bodySimStmtCases exprOpenMain exprOpenTerminals
Libs
  monadsyntax

Theorem compile_assign_tuple_widened_stmt_frag_mem:
  !d ctx func cx lctx RetQ ce ty gs e es tops env stys stvs dtys dtvs atys.
    expr_type e = TupleT atys /\
    body_inv tops ctx ce cx /\ supported_expr tops e /\
    expr_body_pre ce cx env e es /\
    storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
    lowered_value_type ce e = post_value_type ce e /\
    post_value_type ce e = TupleT stys /\
    post_value_type ce e <> expr_type e /\ ~is_memory_view e /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs) /\
    0 < type_memory_size_list stvs /\
    LENGTH gs = LENGTH stys /\ LENGTH dtys = LENGTH gs /\
    (!i. i < LENGTH gs ==>
      type_widens_to (get_tenv cx) (EL i stys) (EL i dtys)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned ce cx (EL i gs) (EL i dtys) (EL i dtvs) /\
      (~is_word_type (EL i dtys) ==>
        type_memory_size (EL i dtvs) + 64 < dimword (:256)) /\
      (!ee v. expr_sim_inv ce cx env ee /\ value_has_type (EL i dtvs) v ==>
        tuple_target_layout ee.scopes (EL i gs) (EL i dtys) (EL i dtvs) v)) /\
    expr_sim_mem ctx func ce cx (expr_type e) e es ==>
    stmt_frag_mem d ctx func cx lctx RetQ ce
      (stmt_env ce lctx ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `lowered_value_type ce e = TupleT stys` by simp[] >>
  drule_all assign_tuple_unstaged_parts >> strip_tac >> gvs[] >>
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

Resume compile_assign_tuple_widened_stmt_frag_mem[normal]:
  `!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (INL v, es_end with gas_obs := tail)` by fs[gas_marked_exec_def] >>
  drule_at (Pos last) tuple_widened_marked_read_typed >> simp[] >>
  disch_then drule >> simp[] >> strip_tac >>
  drule_all tuple_type_value >> strip_tac >> gvs[] >>
  `!i. i < LENGTH gs ==>
      tuple_target_aligned ce cx (EL i gs) (EL i dtys) (EL i dtvs) /\
      tuple_target_layout (es_end with gas_obs := []).scopes
        (EL i gs) (EL i dtys) (EL i dtvs) (EL i vs) /\
      (is_word_type (EL i stys) = is_word_type (EL i dtys)) /\
      type_widens_to (get_tenv cx) (EL i stys) (EL i dtys) /\
      evaluate_type (get_tenv cx) (EL i stys) = SOME (EL i stvs) /\
      value_has_type (EL i stvs) (EL i vs) /\ val_wf (EL i stvs) (EL i vs) /\
      value_has_type (EL i dtvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs) /\
      (is_word_type (EL i dtys) ==> type_memory_size (EL i dtvs) = 32) /\
      (~is_word_type (EL i stys) ==> type_memory_size (EL i dtvs) + 64 < dimword (:256))` by
    (rpt gen_tac >> rpt disch_tac >> irule tuple_widened_runtime_ready >> simp[] >>
     qexists_tac `env` >> simp[]) >>
  suspend "suffix"
QED
Resume compile_assign_tuple_widened_stmt_frag_mem[suffix]:
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `return_buf_frame d ce su t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  drule assign_tuple_widened_targets_suffix_mem >> simp[] >>
  disch_then (qspecl_then [`lctx`, `gs`, `dtys`, `dtvs`, `sb`, `d`] mp_tac) >>
  (impl_tac >- suspend "suffix_pre") >> strip_tac >>
  suspend "compose"
QED
Resume compile_assign_tuple_widened_stmt_frag_mem[suffix_pre]:
  `local_ptrs_reserved ce su` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at su x` by
    (metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  `~block_is_terminated su` by
    (qpat_x_assum `!tail. monad_bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     rename1 `compile_expr ce (TupleT atys) e sa = (vv,mid)` >>
     `expr_body_pre ce cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     gvs[] >>
     `~block_is_terminated mid` by
       (irule compile_expr_open_general >>
        goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
        goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
        metis_tac[]) >>
     drule_all unwrap_value_open >> simp[]) >>
  `~block_is_terminated ss` by
    (drule_all compile_tuple_load_all_open >> simp[]) >>
  simp[] >>
  conj_tac >-
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def] >> metis_tac[]) >>
  `LENGTH stys = LENGTH stvs` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH stvs = LENGTH vs` by metis_tac[vyperTypingTheory.values_have_types_length] >>
  `LENGTH dtys = LENGTH dtvs` by
    (drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >> strip_tac >> gvs[] >> metis_tac[LIST_REL_LENGTH]) >>
  simp[] >>
  conj_tac >- fs[bodySimTheory.body_inv_def] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  `!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields` by fs[expr_sim_inv_def] >>
  simp[] >> conj_tac >- metis_tac[typed_copy_memory_size] >>
  conj_tac >- metis_tac[typed_copy_memory_size] >>
  drule body_inv_mcopy >> simp[]
QED
Resume compile_assign_tuple_widened_stmt_frag_mem[compose]:
  qexistsl_tac [`INL ()`, `ee'`, `OK t'`] >> conj_tac
  >- (pure_rewrite_tac [tuple_targets_source_action] >>
      irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
        |> REWRITE_RULE [APPEND_NIL]) >>
      qexistsl_tac [`es_end with gas_obs := []`, `t`, `ArrayV (TupleV vs)`] >> simp[] >>
      conj_tac
      >- (irule gas_marked_exec_end_gas_obs >> simp[]) >>
      simp[gas_marked_exec_def, gas_marked_path_def,
           gas_explicit_def, gas_prefix_def]) >>
  disj1_tac >> simp[] >> fs[stmt_post_def] >> decide_tac
QED
Resume compile_assign_tuple_widened_stmt_frag_mem[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (pure_rewrite_tac [tuple_targets_source_action] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED
Resume compile_assign_tuple_widened_stmt_frag_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  pop_assum strip_assume_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  pure_rewrite_tac [tuple_targets_source_action] >>
  ONCE_REWRITE_TAC [ignore_bind_bind_value] >>
  irule gas_exempt_cert_error_value >> simp[]
QED
Finalise compile_assign_tuple_widened_stmt_frag_mem
