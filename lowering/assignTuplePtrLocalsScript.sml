(* Counted pointer outcome for tuple assignment into compatible locals. *)
Theory assignTuplePtrLocals
Ancestors
  assignTuplePtrLocalSuccess assignTuplePtrLocalSuffix assignTuplePtrTargets tupleAssignMemory
  tupleLocalStoreProps tupleAssignParts tupleStageProps stmtSimForced bodyPtrDefs stmtFragPtr
  stmtAbortPtr gasSummaryComposePtr exprSimProps exprOperandVar
  exprLoweringProps compileEnv loweringPosts stmtSimDefs stmtSimProps
  vyperInterpreter vyperState vyperValue venomState fragGasPathPtr gasExemptCert
  gasSummary fragGasMode fragGasPath gasContext ptrDiscipline
  stmtSimAssignTuple stmtSimReturn exprLowering stmtLowering fragExec
  valueCopyBytes valueEncoding vyperTyping list finite_map words arithmetic
Libs
  monadsyntax

Theorem eval_assign_tuple_locals_action_ptr[local]:
  eval_stmt cx (Assign (TupleTarget gs) e) =
  bind (bind (eval_expr cx e) (read_result cx))
    (assign_tuple_targets cx (TupleTarget gs))
Proof
  simp[Once evaluate_def, FUN_EQ_THM, bind_def] >> gen_tac >>
  Cases_on `eval_expr cx e x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem compile_assign_tuple_locals_memory_stmt_frag_ptr:
  ids <> [] /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e = expr_type e /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  (EXISTS (\t. ~is_word_type t) tys ==> cenv.ce_target CapMcopy) /\
  (is_memory_view e /\ EXISTS (\t. ~is_word_type t) tys ==>
    type_memory_size (TupleTV tvs) < dimword (:256)) /\
  (!i. i < LENGTH ids ==> ?p sz vt.
    FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type (EL i ids) = SOME vt /\
    if is_word_type (EL i tys) then is_word_type vt else
      (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
      type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
      ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
        type_memory_bytes cenv vt = type_memory_size vtv /\
        0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256)) /\
  (!obs v es1. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := obs) = (INL v,es1) ==> value_has_type (TupleTV tvs) v) /\
  (!obs vs es1 i entry.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL (ArrayV (TupleV vs)),es1) /\ i < LENGTH ids /\
    lookup_scopes (EL i ids) es1.scopes = SOME entry ==>
    if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs)
    else ?vt. cenv.ce_var_type (EL i ids) = SOME vt /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type (EL i vs)) /\
  expr_sim_ptr d ctx PG func cenv cx (TupleT tys) e es ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
    (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `!i. i < LENGTH ids /\ i < LENGTH tys ==> ?p sz vt.
    FLOOKUP cenv.ce_vars (EL i ids) = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type (EL i ids) = SOME vt /\
    (is_word_type vt = is_word_type (EL i tys)) /\
    (~is_word_type vt ==> vt = EL i tys \/ is_bytestring_type vt)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
     simp[] >> strip_tac >> qexistsl_tac [`p`, `sz`, `vt`] >>
     Cases_on `is_word_type (EL i tys)` >> gvs[] >> metis_tac[is_bytestring_word_type]) >>
  drule_all assign_tuple_locals_memory_code_parts >> strip_tac >> gvs[] >>
  `lower_value compile_expr cenv (TupleT tys) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa su` by metis_tac[cs_extends_trans] >>
  `cs_extends su sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa su func` by
    (irule (cj 1 fn_has_code_split) >> simp[] >> qexists_tac `sb` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule forced_then_admissible >>
     qexistsl_tac [`assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids))`, `lctx`] >>
     metis_tac[eval_assign_tuple_locals_action_ptr]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >> suspend "summary") >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[eval_assign_tuple_locals_action_ptr] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[GSYM ignore_bind_def]
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_ptr[summary]:
  rewrite_tac[eval_assign_tuple_locals_action_ptr] >>
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >> conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_ptr_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_ptr[normal]:
  gvs[] >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `?obs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
    (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> metis_tac[]) >>
  `value_has_type (TupleTV tvs) v` by metis_tac[] >>
  Cases_on `assign_tuple_targets cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v
    (es_end with gas_obs := [])` >> rename1 `_ = (res,ee')` >>
  `eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)
    (es with gas_obs := obs) = (res,ee')` by
    (rewrite_tac[eval_assign_tuple_locals_action_ptr] >>
     once_rewrite_tac[bind_def] >> simp[]) >>
  `stmt_res_ok lctx res` by metis_tac[gas_admissible_def] >>
  `res = INL ()` by
    (drule assign_tuple_locals_ok >> disch_then irule >> gvs[stmt_res_ok_def]) >>
  gvs[] >> drule_all tuple_type_value >> strip_tac >> gvs[] >>
  qpat_assum `assign_tuple_targets _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss()) [Once evaluate_def]) >> strip_tac >>
  suspend "layout"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_ptr[layout]:
  `LENGTH ids = LENGTH vs` by
    (drule assign_tuple_target_list_length >> simp[]) >>
  `LENGTH tys = LENGTH tvs /\ LENGTH tvs = LENGTH vs` by
    metis_tac[LIST_REL_LENGTH, values_have_types_length] >>
  `!i. i < LENGTH tys ==> evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by
    fs[LIST_REL_EL_EQN] >>
  `LIST_REL (\t tv. type_memory_bytes cenv t = type_memory_size tv) tys tvs` by
    (irule tuple_element_sizes >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >>
         simp[] >> metis_tac[]) >>
     qexists_tac `get_tenv cx` >> simp[]) >>
  `!i. i < LENGTH tys ==> 0 < type_memory_size (EL i tvs)` by
    (rpt strip_tac >> Cases_on `is_word_type (EL i tys)`
     >- metis_tac[word_type_sizes, DECIDE ``0 < 32``] >>
     qpat_x_assum `!i. i < LENGTH ids ==> _` (qspec_then `i` mp_tac) >> simp[] >>
     strip_tac >> irule compatible_memory_type_positive >> metis_tac[]) >>
  drule tuple_locals_success_initial_assignable_ptr >>
  simp[EVERY_EL] >> disch_tac >>
  `!i. i < LENGTH ids ==> ?id p sz vt entry.
    EL i (MAP (BaseTarget o NameTarget) ids) = BaseTarget (NameTarget id) /\
    lookup_scopes id (es_end with gas_obs := []).scopes = SOME entry /\ entry.assignable /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\ cenv.ce_var_type id = SOME vt /\
    (is_word_type vt = is_word_type (EL i tys)) /\
    (if is_word_type (EL i tys) then store_lays_out (EL i tvs) entry.type (EL i vs) else
      (vt = EL i tys \/ is_bytestring_type vt /\ is_bytestring_type (EL i tys)) /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type (EL i vs) /\
      type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
      type_memory_bytes cenv vt = type_memory_size entry.type /\
      0 < type_memory_size entry.type /\ type_memory_size entry.type + 64 < dimword (:256))` by
    (rpt strip_tac >>
     qpat_assum `!i. i < LENGTH ids ==> ?p sz vt. _` (qspec_then `i` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     `?entry. lookup_scopes (EL i ids) es_end.scopes = SOME entry /\ entry.assignable` by metis_tac[] >>
     qpat_assum `!obs vs es1 i entry. _` drule >> simp[] >>
     disch_then (qspecl_then [`i`, `entry`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qexistsl_tac [`EL i ids`, `p`, `sz`, `vt`, `entry`] >>
     simp[EL_MAP] >> Cases_on `is_word_type (EL i tys)` >> gvs[] >>
     metis_tac[is_bytestring_word_type]) >>
  suspend "suffix"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_ptr[suffix]:
  `!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    type_memory_bytes cenv (EL i tys) = type_memory_size (EL i tvs) /\
    0 < type_memory_size (EL i tvs)` by fs[LIST_REL_EL_EQN] >>
  qmatch_asmsub_abbrev_tac `if flag then _ else comp_return op` >>
  `flag ==> type_memory_size_list tvs < dimword (:256)` by
    (simp[Abbr `flag`] >> metis_tac[type_memory_size_def]) >>
  qpat_x_assum `(if flag then _ else _) su = _`
    (assume_tac o REWRITE_RULE [optional_tuple_stage_code]) >>
  `ptr_buf_ok cenv e op G t` by fs[is_word_type_def] >>
  `(es_end with gas_obs := []).gas_obs = []` by simp[] >>
  `MAP (BaseTarget o NameTarget) ids <> [] /\
    LENGTH (MAP (BaseTarget o NameTarget) ids) = LENGTH tys` by simp[] >>
  drule_at (Pat `compile_tuple_store_all _ _ _ _ _ = _`) assign_tuple_locals_suffix_ptr >>
  disch_then (drule_at (Pat `compile_tuple_load_all _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) _ = _`)) >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`lctx`, `PG`, `cx_dead cx`] mp_tac) >>
  (impl_tac >- (rpt strip_tac >>
    qpat_assum `!i. i < LENGTH ids ==> ?id p sz vt entry. _` (qspec_then `i` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qexistsl_tac [`id`, `p`, `sz`, `vt`, `entry`] >>
    Cases_on `is_word_type (EL i tys)` >> gvs[])) >> strip_tac >>
  suspend "finish"
QED

Resume compile_assign_tuple_locals_memory_stmt_frag_ptr[finish]:
  qexistsl_tac [`INL ()`, `ee''`, `G'`, `tn'`, `OK t'`] >> conj_tac
  >- (irule (SIMP_RULE std_ss [APPEND_NIL]
        (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
      qexistsl_tac [`G`, `es_end`, `t`, `tn`, `ArrayV (TupleV vs)`] >>
      simp[gas_marked_exec_ptr_def]) >>
  disj1_tac >> simp[] >>
  qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_post_def, ghost_inv_gas_obs] >> strip_tac >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  simp[ghost_kept_def]
QED

Finalise compile_assign_tuple_locals_memory_stmt_frag_ptr
