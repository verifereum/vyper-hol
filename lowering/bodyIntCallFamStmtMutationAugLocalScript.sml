(* Direct local AugAssign: counted load/RHS/operator/store composition. *)
Theory bodyIntCallFamStmtMutationAugLocal
Ancestors
  bodyIntCallFamStmtMutationAugLocalEntry bodyIntCallFamStmtMutationAugLocalStore
  bodyIntCallFamStmtMutationBinopCont bodyIntCallJointContract
  stmtSimAugAssign bodyExprPreFacts bodySim stmtSimDefs
  vyperTypeSystem supportedStmts supportedStmtTraverse vyperTypeCallGraph
  exprSimHypsDefs compileEnv loweringSlice bodyIntCallJointStmtSeq
  exprSimSource vyperTypeStatePreservation exprLoweringProps fragExec loweringStateRelDefs

(* Source suffix boundary, independent of the compiler and frame resources. *)
Theorem augassign_local_normal_source:
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  lookup_scopes id es.scopes = SOME entry /\ bop <> In /\ bop <> NotIn /\
  bop_result cx ty bop [ty;expr_type e] entry.value v ee = INL result /\
  write_place cx (MemoryPlace id []) result ee = (INL (),fin) ==>
  evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    entry.type bop entry.value v = INL result /\
  eval_stmt cx (AugAssign ty (NameTarget id) bop e) es = (INL (),fin)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] entry.value v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v of
     INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     entry.type bop entry.value v = INL result` by
    (Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v` >> gvs[]) >>
  simp[] >> drule_all augassign_rhs_normal >>
  disch_then (qspecl_then [`ty`,`bop`] mp_tac) >>
  simp[vyperStateTheory.lift_sum_def,vyperStateTheory.bind_def,
       vyperStateTheory.return_def]
QED

Theorem intcall_augassign_local_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  intcall_stmts_producer fp [AugAssign ty (NameTarget id) bop rhs]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def,eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `type_stmt env fp.jc_ret_ty (AugAssign ty (NameTarget id) bop rhs) =
     SOME env'` by
    gvs[vyperTypeSystemTheory.type_stmt_def,DISJ_IMP_THM,AllCaseEqs()] >>
  `supported_stmt fp.jc_tops bindings
      (AugAssign ty (NameTarget id) bop rhs)` by
    fs[supported_stmt_def] >>
  `stmt_exprs_ok ce (AugAssign ty (NameTarget id) bop rhs)` by fs[] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr rhs)` by
    fs[int_calls_stmt_def] >>
  `!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AugAssign ty (NameTarget id) bop rhs) ==>
      occurs_abi_decode_target target fp.jc_tops` by
    (fs[supported_stmts_expr_exists_list] >> metis_tac[]) >>
  drule_all intcall_augassign_local_rhs_pre >> strip_tac >>
  drule intcall_augassign_local_typing >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `stmt_env ce lctx (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     (AugAssign ty (NameTarget id) bop rhs) sa = (ce',sb)` by
    metis_tac[stmts_env_singleton] >>
  drule_all augassign_local_code_parts >> strip_tac >> gvs[] >>
  `word_value_type ty /\ word_value_type (expr_type rhs)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `word_value entry.value` by
    (fs[expr_sim_inv_def] >>
     metis_tac[lookup_scopes_state_well_typed_value_has_type,word_value_type_typed]) >>
  `is_word_type ty /\ is_word_type (expr_type rhs)` by
    metis_tac[word_value_type_word] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends sa s1 /\ cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `cs_extends s1 sb /\ cs_extends s2 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 fp.jc_func /\ fn_has_code s1 sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s1 s2 fp.jc_func /\ fn_has_code s2 sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s3 fp.jc_func /\ fn_has_code s3 sb fp.jc_func` by
    metis_tac[fn_has_code_split] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  drule_all intcall_augassign_local_load >> strip_tac >>
  suspend "rhs"
QED

Resume intcall_augassign_local_stmt_step[rhs]:
  rename1 `gas_marked_path F _ _ s 0 (OK loaded)` >>
  `gas_admissible (bind (eval_expr fp.jc_cx rhs) (read_result fp.jc_cx))
      expr_res_ok es` by metis_tac[augassign_rhs_admissible] >>
  `supported_expr fp.jc_tops rhs` by fs[supported_stmt_def] >>
  `intcall_expr_res fp ce env es s1 loaded /\ ~loaded.vs_halted /\
   loaded.vs_current_bb = s1.cs_current_bb /\
   loaded.vs_inst_idx = LENGTH s1.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `intcall_forced_producer fp rhs` by metis_tac[] >>
  qpat_x_assum `intcall_forced_producer fp rhs` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (fs[gasSummaryTheory.gas_summary_at_def]
      >- suspend "normal"
      >> suspend "exception") >>
  suspend "exempt"
QED

Resume intcall_augassign_local_stmt_step[exception]:
  `?ex. res = INR ex` by
    (Cases_on `res` >> fs[exprSimDefsTheory.expr_exit_def]) >> gvs[] >>
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (eval_stmt fp.jc_cx (AugAssign ty (NameTarget id) bop rhs))
     (es,s) marks (INR ex) es_end r` by
    (irule augassign_rhs_exception_exec >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     metis_tac[gasSummaryTheory.gas_marked_exec_def]) >>
  simp[gasOutcomeTheory.gas_outcome_def] >> qexists `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INR ex`,`es_end`,`r`] >> simp[intcall_stmt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume intcall_augassign_local_stmt_step[exempt]:
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (eval_target_place fp.jc_cx (NameTarget id)) (es,s) []
     (INL (MemoryPlace id [])) es (OK loaded)` by
    (simp[gasSummaryTheory.gas_marked_exec_def] >>
     simp[eval_target_place_local]) >>
  drule stmtSimDeclGasTheory.gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  simp[gasOutcomeTheory.gas_outcome_def] >>
  metis_tac[augassign_rhs_exempt]
QED

Resume intcall_augassign_local_stmt_step[normal]:
  gvs[] >>
  drule gas_marked_exec_observation >>
  disch_then (qspec_then `[]` assume_tac) >>
  drule_all augassign_binop_ready >> strip_tac >>
  pop_assum (qspecl_then [`fp.jc_func`,`es_end with gas_obs := []`,`fp.jc_ctx`]
    strip_assume_tac) >>
  `intcall_expr_res fp ce env (es_end with gas_obs := []) s2 u /\
   ~u.vs_halted /\ u.vs_current_bb = s2.cs_current_bb /\
   u.vs_inst_idx = LENGTH s2.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `eval_operand cur_op u = SOME (val_to_w256 entry.value)` by
    (drule emitted_insts_emit_op_local >> strip_tac >>
     fs[intcall_expr_cont_def,venomStateTheory.eval_operand_def] >>
     metis_tac[]) >>
  `!x. cur_op = Var x ==> not_fresh_at s2 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `expr_body_pre ce fp.jc_cx env rhs (es with gas_obs :=
      gas_explicit marks loaded.vs_gas_readings ++ [])` by
    simp[] >>
  `?tv. word_value v /\
     evaluate_type (get_tenv fp.jc_cx) (expr_type rhs) = SOME tv /\
     value_has_type tv v` by metis_tac[expr_body_pre_word_result] >>
  `eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (irule exprBopSimPropsTheory.expr_val_rel_word >>
     simp[] >> qexistsl [`fp.jc_cx`,`expr_type rhs`] >> simp[]) >>
  drule_all augassign_binop_admissible >> strip_tac >>
  fs[exprBopSimDefsTheory.binop_frag_def] >>
  `expr_res_ok (bop_result fp.jc_cx ty bop [ty; expr_type rhs]
     entry.value v (es_end with gas_obs := []))` by simp[] >>
  drule_all intcall_binop_frag_words_cont >> strip_tac
  >- suspend "store"
  >> suspend "arithmetic_exit"
QED

Resume intcall_augassign_local_stmt_step[store]:
  gvs[] >>
  rename1 `bop_result _ _ _ _ _ _ es_end = INL result` >>
  `?wr fin. write_place fp.jc_cx (MemoryPlace id []) result
      (es_end with gas_obs := []) = (wr,fin)` by metis_tac[pairTheory.PAIR] >>
  `!m. wr <> INR (Error (TypeError m))` by
    (drule_at (Pos (el 5)) augassign_write_admissible >>
     simp[] >> metis_tac[]) >>
  drule_all stmtSimAssignStoreTheory.write_place_local >> strip_tac >>
  `evaluate_binop (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     entry.type bop entry.value v = INL result /\
   eval_stmt fp.jc_cx (AugAssign ty (NameTarget id) bop rhs)
      (es with gas_obs := gas_explicit marks loaded.vs_gas_readings) = (INL (),fin)` by
    (irule augassign_local_normal_source >> simp[]) >>
  `env' = env` by
    gvs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
  `call_evaluation_safe fp.jc_cx
     (int_calls_stmt (AugAssign ty (NameTarget id) bop rhs))` by
    (fs[intcall_frame_ok_def,
        vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
     metis_tac[]) >>
  `type_stmt env (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
      (AugAssign ty (NameTarget id) bop rhs) = SOME env` by
    (gvs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_inv ce fp.jc_cx env fin` by
    (irule expr_sim_inv_stmt >>
     fs[body_inv_def] >>
     metis_tac[expr_sim_inv_gas_obs]) >>
  `lookup_scopes id es_end.scopes = SOME entry'` by
    gvs[vyperLookupTheory.find_containing_scope_lookup] >>
  `entry'.type = entry.type` by
    (qpat_assum `expr_sim_inv ce fp.jc_cx env es_end`
       (mp_then Any mp_tac expr_sim_inv_local) >>
     disch_then (qspecl_then [`id`,`ty`] mp_tac) >> simp[] >> metis_tac[]) >>
  `store_lays_out entry.type entry'.type result` by
    (simp[] >> irule stmtSimDeclStoreTheory.store_lays_out_typed >>
     metis_tac[]) >>
  suspend "store_resource"
QED

Resume intcall_augassign_local_stmt_step[store_resource]:
  `intcall_joint_res fp ce env (es_end with gas_obs := []) s3 u' /\
   ~u'.vs_halted /\ u'.vs_current_bb = s3.cs_current_bb /\
   u'.vs_inst_idx = LENGTH s3.cs_current_insts` by
    fs[intcall_expr_cont_def,intcall_joint_res_def] >>
  `?w. lookup_var p u' = SOME w` by
    (irule local_word_pointer_live >>
     fs[intcall_joint_res_def,intcall_expr_res_def] >> metis_tac[]) >>
  `sb.cs_next_var = s3.cs_next_var` by
    metis_tac[emitHelperPropsTheory.emitted_insts_emit_void] >>
  `local_ptrs_reserved ce sb /\
   (!x. not_fresh_at s3 x ==> not_fresh_at sb x)` by
    (conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists `s3` >>
         fs[intcall_joint_res_def,intcall_expr_res_def,cs_extends_def]) >>
     rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `s3` >> fs[cs_extends_def]) >>
  `eval_operand res_op u' = SOME (typed_val_to_w256 entry.type result)` by
    metis_tac[exprSimPropsTheory.typed_val_to_w256_word_value] >>
  drule_all intcall_local_word_store_path >> strip_tac >>
  `gas_marked_path F fp.jc_ctx fp.jc_func u 0 (OK u'')` by
    (qpat_assum `gas_marked_path F _ _ u 0 (OK u')`
       (mp_then Any mp_tac fragGasModeTheory.gas_marked_path_then) >> simp[]) >>
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      entry.type bop entry.value v)) (write_place fp.jc_cx (MemoryPlace id [])))
      (es_end with gas_obs := [],u) [] (INL ()) fin (OK u'')` by
    (irule augassign_store_continuation_exec >> simp[] >>
     metis_tac[]) >>
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
      (eval_stmt fp.jc_cx (AugAssign ty (NameTarget id) bop rhs))
      (es,s) marks (INL ()) fin (OK u'')` by
    (irule augassign_rhs_normal_exec >>
     qexistsl [`es_end`,`entry`,`loaded`,`u`,`v`] >>
     gvs[gasSummaryTheory.gas_marked_exec_def]) >>
  suspend "store_finish"
QED

Resume intcall_augassign_local_stmt_step[store_finish]:
  simp[gasOutcomeTheory.gas_outcome_def] >>
  qexists `marks` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INL ()`,`fin`,`OK u''`] >> simp[] >>
  `~block_is_terminated sb` by
    (drule exprOpenPrimitivesTheory.emit_void_terminated >>
     simp[venomInstTheory.is_terminator_def]) >>
  gvs[loweringPostsTheory.stmt_lands_def,stmtSimPropsTheory.cenv_top_ext_refl] >>
  fs[intcall_expr_cont_def] >> disj1_tac >> rpt strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (drule emitted_insts_emit_op_local >> simp[]) >>
  `not_fresh_at s1 x /\ not_fresh_at s2 x` by
    (conj_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  metis_tac[]
QED

Resume intcall_augassign_local_stmt_step[arithmetic_exit]:
  `bop_result fp.jc_cx ty bop [ty;expr_type rhs] entry.value v
     (es_end with gas_obs := []) =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v of
     INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v` >>
  fs[exprSimDefsTheory.expr_exit_def] >>
  rename1 `evaluate_binop _ _ _ _ _ = INR err` >>
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (bind (lift_sum (evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       entry.type bop entry.value v)) (write_place fp.jc_cx (MemoryPlace id [])))
     (es_end with gas_obs := [],u) [] (INR (Error err)) es_end r` by
    simp[gasSummaryTheory.gas_marked_exec_def,vyperStateTheory.bind_def,
         vyperStateTheory.lift_sum_def,vyperStateTheory.raise_def] >>
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
      (eval_stmt fp.jc_cx (AugAssign ty (NameTarget id) bop rhs))
      (es,s) marks (INR (Error err)) es_end r` by
    (irule augassign_rhs_normal_exec >>
     qexistsl [`es_end`,`entry`,`loaded`,`u`,`v`] >>
     gvs[gasSummaryTheory.gas_marked_exec_def]) >>
  qexists `marks` >> disj1_tac >>
  qexistsl [`INR (Error err)`,`es_end`,`r`] >>
  simp[intcall_stmt_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Finalise intcall_augassign_local_stmt_step
