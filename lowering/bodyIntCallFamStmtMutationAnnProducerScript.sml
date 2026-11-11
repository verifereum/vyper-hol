(* Resource-aware singleton declaration producer. *)
Theory bodyIntCallFamStmtMutationAnnProducer
Ancestors
  bodyIntCallFamStmtMutationAnn bodyIntCallFamStmtMutationWordInit
  bodyIntCallFamStmtMutationEmptyInit bodyIntCallFamStmtMutationAggregateInit
  bodyIntCallFamStmtMutationBytesAssign bodyIntCallJointStmtSeq
  bodyIntCallFamStmtMutationBytesContinuation bodyIntCallFamStmtMutationEmptyProducer
  bodyIntCallFamStmtMutationBytesMetadata bodyIntCallFamStmtMutationCopyOpen
  stmtLoweringProps
  bodyIntCallFamStmtMutationDeclAlloc bodyIntCallJointContract
  stmtSimDeclCompose stmtSimDeclSource bodyExprPreFacts exprSimSource
  supportedStmts supportedStmtTraverse vyperTypeCallStackSoundness
  vyperTypeCallGraph stmtSimProps bodySim compileEnv

Theorem intcall_annassign_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) ==>
  intcall_stmts_producer fp [AnnAssign id ty e]
Proof
  strip_tac >>
  Cases_on `has_length_word ty /\ is_empty_value_expr e`
  >- (irule intcall_annassign_empty_stmt_step >> simp[]) >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  `type_stmt env fp.jc_ret_ty (AnnAssign id ty e) = SOME env'` by
    gvs[vyperTypeSystemTheory.type_stmt_def, AllCaseEqs()] >>
  `supported_stmt fp.jc_tops bindings (AnnAssign id ty e)` by
    fs[supported_stmts_list] >>
  `supported_expr fp.jc_tops e` by fs[supported_stmt_def] >>
  `calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)` by
    fs[int_calls_stmt_def] >>
  `call_evaluation_safe fp.jc_cx (int_calls_stmt (AnnAssign id ty e))` by
    (fs[int_calls_stmt_def,intcall_frame_ok_def,call_evaluation_safe_def] >>
     metis_tac[]) >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton] >> strip_tac >>
  `expr_sim_inv ce fp.jc_cx env es` by
    fs[intcall_joint_res_def,intcall_expr_res_def] >>
  `?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv` by
    (fs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs(),
        exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
     metis_tac[vyperTypeSystemTheory.assignable_type_well_formed,
               vyperTypeSystemTheory.well_formed_type_def,
               optionTheory.IS_SOME_EXISTS]) >>
  `!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (AnnAssign id ty e) ==> occurs_abi_decode_target target fp.jc_tops` by
    fs[supported_stmts_expr_exists_list] >>
  Cases_on `is_word_type ty` >- suspend "word" >>
  suspend "nonword"
QED

Resume intcall_annassign_stmt_step[word]:
  `~has_length_word ty` by
    (qspec_then `ty` mp_tac valueCopyBytesTheory.is_bytestring_word_type >>
     Cases_on `ty` >>
     simp[compileEnvTheory.is_word_type_def,
          stmtLoweringTheory.has_length_word_def] >>
     rename1 `ArrayT elem bd` >> Cases_on `bd` >>
     fs[compileEnvTheory.is_word_type_def,stmtLoweringTheory.has_length_word_def]) >>
  drule_all intcall_annassign_word_entry >> strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
      expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_assum `!e. intcall_expr_producer _ _ /\ _`
    (qspec_then `e` strip_assume_tac) >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  suspend "word_compose"
QED

Resume intcall_annassign_stmt_step[word_compose]:
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
  drule (INST_TYPE [alpha |-> ``:unit``]
    stmtReasonVvMemoryTheory.gas_outcome_bind_value) >>
  disch_then irule >> reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[intcall_stmt_exit_def] >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `type_stmt env (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     (AnnAssign id ty e) = SOME env'` by
    (qpat_assum `type_stmt env fp.jc_ret_ty _ = _` mp_tac >>
     pure_rewrite_tac[vyperTypeSystemTheory.type_stmt_def] >>
     disch_then ACCEPT_TAC) >>
  `type_memory_bytes ce ty = 32` by
    metis_tac[entryDecodeStaticPropsTheory.word_type_dec_sizes] >>
  `~block_is_terminated sb` by
    (drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     simp[venomInstTheory.is_terminator_def]) >>
  `not_fresh_at sA (STRING #"%" (toString sa.cs_next_var))` by
    (fs[intcall_expr_res_def,compileEnvTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  fs[wordsTheory.dimword_def] >> suspend "word_suffix"
QED

Resume intcall_annassign_stmt_step[word_suffix]:
  `?ff u. gas_marked_exec F (fp.jc_ctx,fp.jc_func) (new_variable id tv v)
      (mid with gas_obs := [],t') [] (INL ()) ff (OK u) /\
      stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
      cenv_top_ext ce ce' ff.scopes /\
      intcall_joint_res fp ce' env' (ff with gas_obs := []) sb u /\
      (!x wd. not_fresh_at sA x /\ lookup_var x t = SOME wd ==>
              lookup_var x u = SOME wd) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      t.vs_alloca_next <= u.vs_alloca_next` by
    (irule intcall_annassign_word_continuation >> simp[] >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `MEM _ _`)) >>
     simp[venomInstTheory.mk_inst_def] >>
     goal_assum (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `supported_stmt _ _ _`)) >> simp[] >>
     qexists `op` >> simp[]) >>
  simp[gasOutcomeTheory.gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  disj1_tac >> rpt strip_tac >>
  `ce.ce_alloca_locals` by fs[bodySimTheory.body_inv_def] >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  `not_fresh_at sA x` by
    (irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    fs[compileEnvTheory.not_fresh_at_def] >>
  `lookup_var x t = SOME w'` by
    (qpat_x_assum `!op. op <> _ ==> _` (qspec_then `Var x` mp_tac) >>
     simp[venomStateTheory.eval_operand_def]) >>
  metis_tac[]
QED

Resume intcall_annassign_stmt_step[nonword]:
  drule_all intcall_annassign_copy_entry >> strip_tac >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
      expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_assum `!e. intcall_expr_producer _ _ /\ _`
    (qspec_then `e` strip_assume_tac) >>
  qpat_x_assum `intcall_forced_producer _ _` mp_tac >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
  drule (INST_TYPE [alpha |-> ``:unit``]
    stmtReasonVvMemoryTheory.gas_outcome_bind_value) >>
  disch_then irule >> reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res`
      >- fs[exprSimDefsTheory.expr_exit_def] >>
      simp[intcall_stmt_exit_def] >> disj1_tac >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `type_stmt env (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     (AnnAssign id ty e) = SOME env'` by
    (qpat_assum `type_stmt env fp.jc_ret_ty _ = _` mp_tac >>
     pure_rewrite_tac[vyperTypeSystemTheory.type_stmt_def] >>
     disch_then ACCEPT_TAC) >>
  suspend "copy_normal"
QED

Resume intcall_annassign_stmt_step[copy_normal]:
  markerLib.RESUME_TAC >>
  `ce.ce_alloca_locals` by fs[bodySimTheory.body_inv_def] >>
  `~block_is_terminated sb` by suspend "copy_open" >>
  `?ff u. gas_marked_exec F (fp.jc_ctx,fp.jc_func) (new_variable id tv v)
      (mid with gas_obs := [],t') [] (INL ()) ff (OK u) /\
      stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
      cenv_top_ext ce ce' ff.scopes /\
      intcall_joint_res fp ce' env' (ff with gas_obs := []) sb u /\
      (!x wd. not_fresh_at sA x /\ lookup_var x t = SOME wd ==>
              lookup_var x u = SOME wd) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      t.vs_alloca_next <= u.vs_alloca_next` by
    (Cases_on `is_bytestring_type ty` >- suspend "bytes_join" >>
     irule intcall_annassign_aggregate_continuation >> simp[] >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `MEM _ _`)) >>
     goal_assum (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `supported_stmt _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  suspend "copy_frame"
QED

Resume intcall_annassign_stmt_step[copy_frame]:
  markerLib.RESUME_TAC >>
  simp[gasOutcomeTheory.gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  disj1_tac >> rpt strip_tac >>
  drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
  drule emitHelperPropsTheory.emit_inst_extends >> strip_tac >>
  `not_fresh_at sA x` by
    (irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[]) >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    fs[compileEnvTheory.not_fresh_at_def] >>
  `lookup_var x t = SOME w'` by
    (qpat_x_assum `!op. op <> _ ==> _` (qspec_then `Var x` mp_tac) >>
     simp[venomStateTheory.eval_operand_def]) >>
  metis_tac[]
QED

Resume intcall_annassign_stmt_step[bytes_join]:
  markerLib.RESUME_TAC >>
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    fs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
  `expr_sim_inv ce' fp.jc_cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  drule_all bodyIntCallFamStmtReturnEndpointTypesTheory.return_post_type_widens >> strip_tac >>
  drule_all bodyIntCallFamStmtReturnEndpointTypesTheory.marked_forced_destination_typed >> strip_tac >>
  `expr_body_pre ce' fp.jc_cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  `bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (qspec_then `[]` mp_tac o CONJUNCT1 o
        REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >> simp[]) >>
  `ce'.ce_func_return_type = build_func_return_type fp.jc_tops /\
   supported_program fp.jc_tops /\
   get_module_code fp.jc_cx NONE = SOME fp.jc_tops` by
    fs[bodySimTheory.body_inv_def] >>
  `value_runtime_typed env (lowered_value_type ce' e) v` by
    (irule memoryLocalRhsPropsTheory.memory_rhs_read_lowered_typed >>
     metis_tac[]) >>
  drule_all memoryLocalRhsPropsTheory.memory_rhs_runtime_layout >> strip_tac >>
  drule_all bodyIntCallFamStmtReturnEndpointTypesTheory.marked_forced_post_typed >> strip_tac >>
  drule_all bodyDeclCopyMemoryTheory.declare_local_memory_types_mem >> strip_tac >>
  suspend "bytes_metadata_join"
QED

Resume intcall_annassign_stmt_step[bytes_metadata_join]:
  markerLib.RESUME_TAC >>
  `is_bytestring_type (expr_type e)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  `post_value_type ce' e = expr_type e` by simp[] >>
  `type_memory_bytes ce' (expr_type e) = type_memory_size tv''` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_alloc_ok ce' (expr_type e)` by
    metis_tac[exprSimHypsTheory.alloc_limits_expr_type_alloc_ok,
              exprSimHypsDefsTheory.expr_body_pre_def] >>
  `type_memory_size tv'' + 64 < dimword (:256)` by
    (irule bodyIntCallJointStmtBoundaryTheory.intcall_type_alloc_headroom >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  `type_memory_bytes ce' (expr_type e) + 64 < dimword (:256)` by simp[] >>
  `is_bytestring_type (lowered_value_type ce' e) /\
   type_memory_bytes ce' (lowered_value_type ce' e) <=
     type_memory_bytes ce' (expr_type e)` by
    (irule intcall_bytes_lowered_class >> metis_tac[]) >>
  `type_memory_size tv' + 64 < dimword (:256)` by decide_tac >>
  irule intcall_annassign_bytes_continuation >> simp[] >>
  goal_assum (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `MEM _ _`)) >>
  goal_assum (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `supported_stmt _ _ _`)) >>
  simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl [`marks`,`tv'`] >> gvs[]
QED

Resume intcall_annassign_stmt_step[copy_open]:
  markerLib.RESUME_TAC >>
  `~block_is_terminated sA` by
    (drule exprOpenTerminalsTheory.emit_inst_nonterminator_open >>
     simp[venomInstTheory.is_terminator_def]) >>
  `?raw ee. eval_expr fp.jc_cx e
      (es with gas_obs := gas_explicit marks t.vs_gas_readings) = (INL raw,ee)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (qspec_then `[]` mp_tac o CONJUNCT1 o
        REWRITE_RULE [gasSummaryTheory.gas_marked_exec_def]) >>
     simp[vyperStateTheory.bind_def,AllCaseEqs()] >> metis_tac[]) >>
  `~block_is_terminated sV` by
    (irule exprOpenMainTheory.compile_expr_open_general >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     qexistsl [`fp.jc_ctx`,`env`,`fp.jc_tops`] >>
     fs[intcall_expr_res_def,exprLoweringPropsTheory.stmt_state_rel_def,
        compileEnvTheory.state_rel_def]) >>
  `~block_is_terminated sB` by
    (drule_all exprOpenTerminalsTheory.unwrap_value_open >> simp[]) >>
  irule intcall_memory_copy_open >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  fs[bodySimTheory.body_inv_def]
QED

Finalise intcall_annassign_stmt_step
