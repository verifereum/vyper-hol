(* Empty length-word declarations use the ordinary expression producer. *)
Theory bodyIntCallFamStmtMutationEmptyProducer
Ancestors
  bodyIntCallFamStmtMutationEmptyInit bodyIntCallFamStmtMutationEntry
  bodyIntCallJointStmtSeq stmtSimDeclCompose stmtSimDeclSource bodyExprPreFacts
  exprSimSource supportedStmts supportedStmtTraverse vyperTypeCallStackSoundness
  vyperTypeCallGraph stmtSimProps bodySim compileEnv exprLoweringProps
  bodyDeclCopyMemory fragExec loweringHalt bodyIntCallJointContract stmtSimDeclMem

Theorem intcall_annassign_empty_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\ has_length_word ty /\ is_empty_value_expr e ==>
  intcall_stmts_producer fp [AnnAssign id ty e]
Proof
  strip_tac >>
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
  drule stmt_env_annassign >> strip_tac >>
  drule_all intcall_pending_declaration_pre >> strip_tac >>
  `ce.ce_alloca_locals` by fs[body_inv_def] >>
  drule_all declare_local_ptr >> strip_tac >>
  suspend "compile"
QED

Resume intcall_annassign_empty_stmt_step[compile]:
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once stmtLoweringTheory.compile_stmt_def,
       stmtLoweringTheory.emit_local_alloca_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_inst ALLOCA _ _ _ = (au,sA)` >> Cases_on `au` >>
  rename1 `compile_expr ce' (expr_type e) e sA = (vv,sB)` >>
  `cs_extends sa st` by fs[cs_extends_def] >>
  `cs_extends st sA` by metis_tac[cs_extends_emit_inst] >>
  `cs_extends sA sB` by metis_tac[compile_expr_grows] >>
  `cs_extends sB sb` by
    (fs[GSYM emitHelperTheory.emit_inst_def, emitHelperTheory.emit_void_def] >>
     metis_tac[cs_extends_emit_inst]) >>
  `fn_has_code sa sA fp.jc_func /\ fn_has_code sA sB fp.jc_func /\
   fn_has_code sB sb fp.jc_func` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `id NOTIN FDOM env.var_types` by
    gvs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
  qpat_assum `st = _` (fn th =>
    qpat_x_assum `emit_inst ALLOCA _ _ _ = _`
      (assume_tac o REWRITE_RULE [GSYM th])) >>
  drule_all (intcall_declaration_alloca_prefix |>
    Q.INST [`p` |-> `STRING #"%" (toString sa.cs_next_var)`] |> SRULE []) >>
  strip_tac >> suspend "expr"
QED

Resume intcall_annassign_empty_stmt_step[expr]:
  `gas_admissible (eval_expr fp.jc_cx e) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  qpat_assum `!e. intcall_expr_producer _ _ /\ _`
    (qspec_then `e` strip_assume_tac) >>
  qpat_x_assum `intcall_expr_producer _ _` mp_tac >>
  rewrite_tac[intcall_expr_producer_def] >>
  disch_then drule_all >> strip_tac >> suspend "compose"
QED

Resume intcall_annassign_empty_stmt_step[compose]:
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  drule eval_annassign_action >>
  disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
  rewrite_tac[vyperStateTheory.bind_assoc] >>
  drule (INST_TYPE [alpha |-> ``:unit``]
    exprSimSubscriptMapTheory.gas_outcome_bind_result_exec) >>
  disch_then irule >>
  reverse conj_tac >- (rpt strip_tac >> Cases_on `res`
    >- fs[exprSimDefsTheory.expr_exit_def] >>
    gvs[intcall_stmt_exit_def] >> disj1_tac >>
    metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >> suspend "normal"
QED

Resume intcall_annassign_empty_stmt_step[normal]:
  `well_typed_expr env e /\ type_widens_to env.type_defs (expr_type e) ty` by
    fs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `!tail. eval_expr fp.jc_cx e
    (es with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
    (INL v,mid with gas_obs := tail)` by
    fs[gasSummaryTheory.gas_marked_exec_def] >>
  `v = Value (default_value tv)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >>
     metis_tac[memoryLocalRhsPropsTheory.memory_rhs_empty_eval_destination]) >>
  gvs[vyperStateTheory.read_result_def,vyperStateTheory.bind_return] >>
  `type_stmt env (if fp.jc_ret_ty = NoneT then BaseT BoolT else fp.jc_ret_ty)
     (AnnAssign id ty e) = SOME env'` by
    (qpat_assum `type_stmt env fp.jc_ret_ty _ = _` mp_tac >>
     pure_rewrite_tac[vyperTypeSystemTheory.type_stmt_def] >>
     disch_then ACCEPT_TAC) >>
  `type_memory_bytes ce ty = type_memory_size tv` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  `type_memory_bytes ce ty < dimword (:256)` by
    (fs[bodySimTheory.stmt_exprs_ok_def,allocLimitsTheory.alloc_limits_stmt_def,
        wordsTheory.dimword_def] >> decide_tac) >>
  `~block_is_terminated sb` by
    (drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     simp[venomInstTheory.is_terminator_def]) >>
  `not_fresh_at sA (STRING #"%" (toString sa.cs_next_var))` by
    (fs[intcall_expr_res_def,compileEnvTheory.local_ptrs_reserved_def] >>
     metis_tac[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
     [Lit (n2w (type_memory_bytes ce ty))]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fp.jc_func)` by
    (drule bodyDeclMemoryCoreTheory.annassign_setup_shape >>
     simp[] >> disch_then (qspecl_then [`fp.jc_func`,`es`] mp_tac) >>
     fs[intcall_joint_res_def,intcall_expr_res_def]) >>
  suspend "suffix"
QED

Resume intcall_annassign_empty_stmt_step[suffix]:
  `?ff u. gas_marked_exec F (fp.jc_ctx,fp.jc_func)
      (new_variable id tv (default_value tv))
      (mid with gas_obs := [],t') [] (INL ()) ff (OK u) /\
      stmt_lands lctx sb (INL ()) u /\ ~u.vs_halted /\
      cenv_top_ext ce ce' ff.scopes /\
      intcall_joint_res fp ce' env' (ff with gas_obs := []) sb u /\
      (!x wd. not_fresh_at sA x /\ lookup_var x t = SOME wd ==>
              lookup_var x u = SOME wd) /\
      (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
               FLOOKUP u.vs_allocas aid = SOME b) /\
      t.vs_alloca_next <= u.vs_alloca_next` by
    (irule intcall_annassign_empty_continuation >> simp[] >>
     goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `MEM _ _`)) >>
     simp[venomInstTheory.mk_inst_def] >>
     goal_assum (drule_at (Pat `intcall_expr_cont _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `intcall_joint_res _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `supported_stmt _ _ _`)) >> simp[]) >>
  suspend "package"
QED

Resume intcall_annassign_empty_stmt_step[package]:
  simp[gasOutcomeTheory.gas_outcome_def] >> qexists `[]` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  goal_assum (drule_at Any) >> simp[] >>
  disj1_tac >> rpt strip_tac >>
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

Finalise intcall_annassign_empty_stmt_step
