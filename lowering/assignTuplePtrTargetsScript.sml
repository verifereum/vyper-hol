(* RHS outcome composition for the supported mixed-target tuple branch. *)
Theory assignTuplePtrTargets
Ancestors
  assignTuplePtrSuffix tupleAssignParts tupleStageProps stmtSimForced
  bodyPtrDefs stmtFragPtr stmtAbortPtr gasSummaryComposePtr exprSimProps
  exprOperandVar exprLoweringProps compileEnv loweringPosts stmtSimDefs stmtSimProps
  vyperInterpreter vyperState vyperValue venomState fragGasPathPtr gasExemptCert
  gasSummary fragGasMode fragGasPath gasContext ptrDiscipline
  stmtSimAssignTupleTargets stmtSimAssignTuple exprLowering stmtLowering
  fragExec valueEncoding list finite_map words arithmetic
Libs
  monadsyntax

Theorem eval_assign_tuple_action_ptr[local]:
  eval_stmt cx (Assign (TupleTarget gs) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (assign_tuple_targets cx (TupleTarget gs))
Proof
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem compile_assign_tuple_targets_stmt_frag_ptr:
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
  (!obs v es1. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := obs) = (INL v,es1) ==>
    value_has_type (TupleTV tvs) v) /\
  (!obs vs es1 i.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH gs ==>
    tuple_target_layout es1.scopes (EL i gs) (EL i tys) (EL i tvs) (EL i vs)) /\
  gs <> [] /\ expr_sim_ptr d ctx PG func cenv cx (TupleT tys) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assign (TupleTarget gs) e))
    (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_tuple_targets_code_parts >> strip_tac >> gvs[] >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (irule (cj 1 fn_has_code_split) >> simp[] >> qexists_tac `sb` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >>
     qexistsl_tac [`assign_tuple_targets cx (TupleTarget gs)`, `lctx`] >>
     metis_tac[eval_assign_tuple_action_ptr]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_assign_tuple_action_ptr] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assign_tuple_targets_stmt_frag_ptr[summary]:
  rewrite_tac[eval_assign_tuple_action_ptr] >>
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_ptr_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assign_tuple_targets_stmt_frag_ptr[normal]:
  gvs[] >>
  drule gas_marked_exec_ptr_exec >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `?obs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
    (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  `!i. i < LENGTH gs ==>
    tuple_target_aligned cenv cx (EL i gs) (EL i tys) (EL i tvs) /\
    tuple_target_layout (es_end with gas_obs := []).scopes (EL i gs) (EL i tys) (EL i tvs)
      (EL i (case v of ArrayV (TupleV vs) => vs | _ => []))` by
    (drule_all stmtSimReturnTheory.tuple_type_value >> strip_tac >> gvs[] >>
     rpt strip_tac >>
     qpat_x_assum `!obs vs es1 i. _` drule >> simp[]) >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  `ptr_buf_ok cenv e op G t` by fs[is_word_type_def] >>
  `(es_end with gas_obs := []).gas_obs = []` by simp[] >>
  drule_all assign_tuple_targets_suffix_ptr >>
  disch_then (qspecl_then [`lctx`, `PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "finish"
QED

Resume compile_assign_tuple_targets_stmt_frag_ptr[finish]:
  qexistsl_tac [`INL ()`, `ee'`, `G'`, `tn'`, `OK t'`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      qexistsl_tac [`G`, `es_end`, `t`, `tn`, `v`] >>
      simp[gas_marked_exec_ptr_def]) >>
  disj1_tac >> simp[] >>
  qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_post_def, ghost_inv_gas_obs] >> strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_def]
QED

Finalise compile_assign_tuple_targets_stmt_frag_ptr
