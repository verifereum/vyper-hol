(* A valued return of the external frame whose value is an internal
   call's result laid out at the callee's declared return type
   (lowered_value_type differs from expr_type, other than as a bytestring).
   Besides expr_post, it takes the return expression's memory simulations
   expr_sim_mem and expr_vv_sim_mem at every type, which frame_ret_ok_mem
   provides. *)
Theory externalReturnWidenedCallMem
Ancestors
  externalReturnNormalizedMem incompatibleReturnLayout
  externalReturnLeafMem externalNormalizePremises typedNormalizeRankMem
  nonreentrantExit
  stmtSimDefs loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect fragExecMem bodyMemoryDefs
  entryHaltMem bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs

val _ = Parse.hide "body";

Theorem external_frame_ret_widened_call_mem:
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
       ~(lowered_value_type cenv' e = expr_type e \/
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
       (!ty. expr_sim_mem unit.cu_context func cenv'
               (initial_evaluation_context am.sources am.layouts tx NONE)
               ty e es /\
             expr_vv_sim_mem unit.cu_context func cenv'
               (initial_evaluation_context am.sources am.layouts tx NONE)
               ty e es) /\
       t.vs_current_bb = s1.cs_current_bb /\
       t.vs_inst_idx = LENGTH s1.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       ~t.vs_halted ==>
       ?fuel r. run_from fuel unit.cu_context func t = r /\ exit_result r /\
                mem_safe_run fuel unit.cu_context func t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env e` by
    (qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
     simp[type_stmt_def, AllCaseEqs()]) >>
  drule_all incompatible_return_layout_intcall >> strip_tac >>
  qpat_x_assum `e = _` SUBST_ALL_TAC >>
  `expr_type (Call ann (IntCall fid) xs drv) = ann` by simp[vyperASTTheory.expr_type_def] >>
  `type_widens_to
     (get_tenv (initial_evaluation_context am.sources am.layouts tx NONE))
     ann ret` by
    (`env.type_defs =
      get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)` by
       (qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
        simp[exprSimHypsDefsTheory.expr_sim_inv_def,
          vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     qpat_x_assum `IS_SOME (type_stmt _ _ _)` mp_tac >>
     simp[type_stmt_def, AllCaseEqs()]) >>
  `~is_word_type ret` by metis_tac[typedMemoryCopyTheory.typed_copy_word_widening] >>
  `~(is_bytestring_type
       (lowered_value_type cenv' (Call ann (IntCall fid) xs drv)) /\
     is_bytestring_type ret)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `lowered_value_type cenv' (Call ann (IntCall fid) xs drv) <> ret` by
    metis_tac[vyperTypeArgFitsTheory.type_widens_to_antisym] >>
  drule_all external_frame_ret_value_normalized_run_mem >> simp[]
QED
