(* Actual expression-backed external return, with source runtime typing. *)
Theory externalReturnDirectMem
Ancestors
  externalReturnLeafMem externalNormalizePremises externalReturnPrefix
  externalReturnZeroLayout externalReturnZeroSource externalReturnDestinationMem
  externalReturnAbiMetadata externalReturnSelectedMetadata
  externalReturnDirectWindowMem externalReturnDirectSource vyperTypeArgFits
  externalReturnEncoderSites externalReturnLiveWindowResources
  externalReturnEncoderSuffixMem exprOperandVar returnValueTyped externalRawReturnType
  nonreentrantExit stmtSimDefs loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem bodyMemoryDefs
  entryHaltMem loweringPtrCorrect bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs

val _ = Parse.hide "body";

Theorem external_frame_ret_value_direct_run_mem:
  !tops rpolicy unit am tx ret vs mut args fbody env0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa0 func.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env0 /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa0) ==>
    !cenv' env lctx e es sa sb cenv'' s0 op s1 ee v t.
       same_frame cenv cenv' /\
       (lowered_value_type cenv' e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type cenv' e) /\
        arg_type_fits (lowered_value_type cenv' e) (expr_type e)) /\
       expr_sim_inv cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
       stmt_exprs_ok cenv' (Return (SOME e)) /\
       IS_SOME (type_stmt env ret (Return (SOME e))) /\
       call_evaluation_safe
         (initial_evaluation_context am.sources am.layouts tx NONE)
         (int_calls_stmt (Return (SOME e))) /\
       stmt_env cenv' lctx ret (Return (SOME e)) sa = (cenv'', sb) /\
       lower_value compile_expr cenv' ret e sa = (op, s1) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv' sa /\ ~block_is_terminated sa /\
       stmt_state_rel unit.cu_context func cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) es s0 /\
       alloca_history func s0 /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       expr_post unit.cu_context func cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE)
         e es sa s1 s0 ee v op t /\
       (?gs ee'.
          bind (eval_expr
                  (initial_evaluation_context am.sources am.layouts tx NONE) e)
            (read_result
               (initial_evaluation_context am.sources am.layouts tx NONE))
            (es with gas_obs := gs) = (INL v, ee')) /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ~t.vs_halted /\
       ~(~is_word_type ret /\
         ~(is_bytestring_type (lowered_value_type cenv' e) /\
           is_bytestring_type ret) /\
         lowered_value_type cenv' e <> ret) ==>
       ?fuel r. run_from fuel unit.cu_context func t = r /\ exit_result r /\
                mem_safe_run fuel unit.cu_context func t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_package_frame_exit >> strip_tac >>
  qmatch_asmsub_abbrev_tac `expr_post ctx func cenv' cx` >>
  qpat_x_assum `?gs ee'. _` strip_assume_tac >>
  drule_all return_value_typed >> strip_tac >>
  `compile_external_return (SOME op) (is_word_type ret) cenv'.ce_raw_return
     cenv'.ce_ret_enc_info cenv'.ce_max_return_size F
     (FST (SND cenv'.ce_nonreentrant))
     (FST (SND (SND cenv'.ce_nonreentrant)))
     (SND (SND (SND cenv'.ce_nonreentrant))) s1 = ((),sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `cenv'.ce_return_pc = _` mp_tac >>
     qpat_x_assum `FST cenv'.ce_nonreentrant = _` mp_tac >>
     qpat_x_assum `~(~is_word_type ret /\ _ /\ _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       pairTheory.UNCURRY] >> rpt strip_tac >> gvs[comp_return_def] >>
     qmatch_goalsub_abbrev_tac `r = ((),SND r)` >>
     Cases_on `r` >> simp[]) >>
  suspend "dispatch"
QED

Resume external_frame_ret_value_direct_run_mem[dispatch]:
  `!x. op = Var x ==> not_fresh_at s1 x` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `local_ptrs_reserved _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[compile_lower_value_var]) >>
  `fn_has_code s1 sb func` by
    (drule return_value_code_prefix >> disch_then drule >> strip_tac >>
     drule (cj 2 compile_expr_grows) >> strip_tac >>
     drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  Cases_on `cenv'.ce_raw_return`
  >- suspend "raw" >>
  Cases_on `is_word_type ret`
  >- suspend "word" >>
  suspend "aggregate"
QED

Resume external_frame_ret_value_direct_run_mem[word]:
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `fn_has_code s1 sb func` mp_tac >>
  qpat_x_assum `!x. op = Var x ==> _` mp_tac >>
  qpat_x_assum `stmt_state_rel ctx func cenv' cx ee t` mp_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  qpat_x_assum `~t.vs_halted` mp_tac >>
  qpat_x_assum `t.vs_current_bb = _` mp_tac >>
  qpat_x_assum `t.vs_inst_idx = _` mp_tac >>
  qpat_x_assum `is_word_type ret` mp_tac >>
  qpat_x_assum `~cenv'.ce_raw_return` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  gvs[expr_val_rel_def] >>
  drule_all external_return_word_value_mem >>
  rewrite_tac[frag_exec_mem_def] >>
  disch_then (qspecl_then [`func`, `t`] mp_tac) >> simp[] >>
  metis_tac[]
QED

Resume external_frame_ret_value_direct_run_mem[raw]:
  drule_all external_package_raw_flag >> strip_tac >>
  `lookup_raw_return_or_F (NONE : num option) tx.function_name External tops` by
    metis_tac[] >>
  drule_all source_typing_raw_return_type >> strip_tac >>
  `is_bytestring_type (expr_type e)` by
    (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
     qpat_x_assum `ret = BaseT (BytesT (Dynamic _))` SUBST1_TAC >>
     rpt (pop_assum kall_tac) >>
     simp[type_stmt_def, type_widens_to_def, AllCaseEqs()] >>
     Cases_on `expr_type e` >> simp[arg_type_fits_def, is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[arg_type_fits_def, is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     simp[arg_type_fits_def, is_bytestring_type_def]) >>
  suspend "raw_leaf"
QED

Resume external_frame_ret_value_direct_run_mem[raw_leaf]:
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `fn_has_code s1 sb func` mp_tac >>
  qpat_x_assum `!x. op = Var x ==> _` mp_tac >>
  qpat_x_assum `stmt_state_rel ctx func cenv' cx ee t` mp_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `evaluate_type _ _ = SOME tv` mp_tac >>
  qpat_x_assum `value_has_type tv v` mp_tac >>
  qpat_x_assum `is_bytestring_type (expr_type e)` mp_tac >>
  qpat_x_assum `~t.vs_halted` mp_tac >>
  qpat_x_assum `t.vs_current_bb = _` mp_tac >>
  qpat_x_assum `t.vs_inst_idx = _` mp_tac >>
  qpat_x_assum `cenv'.ce_raw_return` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  qpat_x_assum `cenv'.ce_raw_return` (SUBST_ALL_TAC o EQT_INTRO) >>
  drule_all external_return_raw_value_mem >>
  rewrite_tac[frag_exec_mem_def] >>
  disch_then (qspecl_then [`func`, `t`] mp_tac) >> simp[] >>
  metis_tac[]
QED

Resume external_frame_ret_value_direct_run_mem[aggregate]:
  drule_all direct_return_layout_split >> disch_then assume_tac >>
  `ret <> NoneT` by metis_tac[valued_return_type_not_none] >>
  drule_all external_package_encoder_admissible >> strip_tac >>
  `cenv'.ce_is_external` by suspend "external_flag" >>
  `return_buffer_ok cenv'` by
    (qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
     simp[stmt_exprs_ok_def, stmt_valued_return_def]) >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `type_widens_to (get_tenv cx) (expr_type e) ret` by
    (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
     simp[type_stmt_def, AllCaseEqs()]) >>
  suspend "aggregate_resources"
QED

Resume external_frame_ret_value_direct_run_mem[external_flag]:
  qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
  qpat_x_assum `compile_register_positional_args _ _ _ _ = _` mp_tac >>
  qpat_x_assum `same_frame _ _` mp_tac >>
  qpat_x_assum `ret <> NoneT` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  drule entryStateRelTheory.compile_register_positional_args_cenv >> strip_tac >>
  `cenv0.ce_is_external` by
    (qpat_x_assum `set_external_package_target _ _ = _` mp_tac >>
     simp[package_external_fn_def, set_external_package_target_def] >>
     strip_tac >> gvs[update_cenv_nonreentrant_def] >>
     simp[update_cenv_ret_abi_def, build_compile_env_def, pairTheory.UNCURRY]) >>
  `cenv.ce_is_external` by
    (qpat_x_assum `_ = _ with ce_vars := _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `same_frame _ _`
    (strip_assume_tac o REWRITE_RULE [same_frame_def]) >>
  `cenv'.ce_is_external = cenv.ce_is_external` by
    (qpat_x_assum `_ with <|ce_vars := _; ce_var_type := _;
      ce_dynarray_capacity := _|> = _` (SUBST1_TAC o SYM) >> simp[]) >>
  simp[]
QED

Resume external_frame_ret_value_direct_run_mem[aggregate_resources]:
  drule_all type_widens_to_value_has_type >> strip_tac >>
  qpat_x_assum `Abbrev (cx = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all selected_external_frame_source_abi_metadata >> strip_tac >>
  `cenv'.ce_max_return_size < dimword (:256)` by
    (fs[return_buffer_ok_def, wordsTheory.dimword_def] >> decide_tac) >>
  Cases_on `val_footprint tv v = 0`
  >- suspend "zero_layout" >>
  `0 < val_footprint tv v` by decide_tac >>
  drule_all direct_return_expression_window >> strip_tac >>
  suspend "positive_window"
QED

Resume external_frame_ret_value_direct_run_mem[positive_window]:
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  drule compile_external_return_abi_parts >> simp[] >> strip_tac >>
  `cs_extends s1 sa'` by
    (mp_tac (Q.SPECL [`cenv'.ce_max_return_size`, `s1`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sa' sb'` by
    (mp_tac (cj 2 ci_mono_compile_abi_encode) >>
     disch_then (qspecl_then [`buf.buf_operand`, `op`, `cenv'.ce_ret_enc_info`, `sa'`] mp_tac) >>
     asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sb' sb` by
    (mp_tac (Q.SPECL [`RETURN`, `[buf.buf_operand; len]`, `[]`, `sb'`]
       ci_mono_emit_inst) >> asm_rewrite_tac[ci_mono_def] >> simp[]) >>
  `cs_extends sa' sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code sa' sb' func /\ fn_has_code sb' sb func` by
    (irule fn_has_code_split >> metis_tac[]) >>
  `ci_mono sa (SND (lower_value compile_expr cenv' ret e sa))` by
    (irule ci_mono_lower_value_cfn >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sa s1` by
    (qpat_x_assum `ci_mono sa (SND _)` mp_tac >> asm_rewrite_tac[] >> simp[]) >>
  `local_ptrs_reserved cenv' s1` by
    metis_tac[compiler_ci_mono_reserved] >>
  `local_ptrs_reserved cenv' sa'` by
    (mp_tac (Q.SPECL [`cenv'.ce_max_return_size`, `s1`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[] >> simp[] >> strip_tac >>
     metis_tac[compiler_ci_mono_reserved]) >>
  `~is_word_type (expr_type e)` by
    metis_tac[valueCopyBytesTheory.is_bytestring_word_type] >>
  `LENGTH (enc at rv) <= cenv'.ce_max_return_size` by metis_tac[] >>
  `s1.cs_next_id <= s1.cs_next_id` by simp[] >>
  drule_all direct_encoder_allocate_window >> strip_tac >>
  drule_all abi_encoder_return_safe_exit >> strip_tac >>
  metis_tac[memContinuationExitTheory.mem_cont_sim_safe_exit]
QED

Resume external_frame_ret_value_direct_run_mem[zero_layout]:
  drule_all selected_external_zero_source_metadata >> strip_tac >>
  drule_all typed_zero_return_layout >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[] >>
  `0 <= cenv'.ce_max_return_size` by simp[] >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  drule_all external_return_static_value_mem >>
  rewrite_tac[frag_exec_mem_def] >>
  disch_then (qspecl_then [`func`, `t`] mp_tac) >> simp[] >>
  metis_tac[]
QED

Finalise external_frame_ret_value_direct_run_mem
