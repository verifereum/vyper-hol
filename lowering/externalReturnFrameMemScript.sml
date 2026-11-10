(* The external frame's return sequences, after the returned expression,
   run memory-safely to an exit.  Stated at the run_from level, where the
   return leaves live; loweringMemFrameRet lifts them to the counted
   statement contract. *)
Theory externalReturnFrameMem
Ancestors
  externalReturnPrefix externalReturnValueMem externalReturnWidenedCallMem
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

(* The selected external function's frame (d = NONE, ce_return_pc = NONE):
   every return sequence runs to an exit, checking memory on every step.
   The first conjunct places a valued return's value code before the rest
   of its sequence.
   Return NONE from its start s0; Return e once e's value is in place
   (expr_post at t), through the rest of the sequence: optional
   normalization into a fresh buffer, then the raw, word, static-copy or
   ABI-encoder return. *)
Theorem external_frame_ret_run_mem:
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
    (!cenv' lctx e sa sb cenv'' op s1.
       same_frame cenv cenv' /\
       stmt_env cenv' lctx ret (Return (SOME e)) sa = (cenv'', sb) /\
       lower_value compile_expr cenv' ret e sa = (op, s1) ==>
       cs_extends s1 sb) /\
    (!cenv' env lctx es sa sb cenv'' s0.
       same_frame cenv cenv' /\
       expr_sim_inv cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
       IS_SOME (type_stmt env ret (Return NONE)) /\
       stmt_env cenv' lctx ret (Return NONE) sa = (cenv'', sb) /\
       fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
       local_ptrs_reserved cenv' sa /\ ~block_is_terminated sa /\
       stmt_state_rel unit.cu_context func cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) es s0 /\
       alloca_history func s0 /\ ~s0.vs_halted /\
       s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
       ?fuel r. run_from fuel unit.cu_context func s0 = r /\ exit_result r /\
                mem_safe_run fuel unit.cu_context func s0) /\
    (!cenv' env lctx e es sa sb cenv'' s0 op s1 ee v t.
       same_frame cenv cenv' /\
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
       (?fuel r. run_from fuel unit.cu_context func t = r /\ exit_result r /\
                mem_safe_run fuel unit.cu_context func t) \/
       stmt_frag_mem NONE unit.cu_context func
         (initial_evaluation_context am.sources am.layouts tx NONE) lctx (\v es r. T) cenv'
         (stmt_env cenv' lctx ret (Return (SOME e)))
         (eval_stmt (initial_evaluation_context am.sources am.layouts tx NONE)
           (Return (SOME e))) es)
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (rpt strip_tac >> drule_all return_value_code_prefix >> simp[])
  >- (rpt strip_tac >> drule_all external_package_frame_exit >> strip_tac >>
      drule_all return_none_external_run_mem >> simp[])
  >> rpt strip_tac >>
  Cases_on `lowered_value_type cenv' e = expr_type e \/
            is_bytestring_type (expr_type e) /\
            is_bytestring_type (lowered_value_type cenv' e) /\
            arg_type_fits (lowered_value_type cenv' e) (expr_type e)`
  >- (disj1_tac >>
      drule_all (Ho_Rewrite.PURE_REWRITE_RULE [PULL_EXISTS] external_frame_ret_value_run_mem) >>
      simp[]) >>
  disj2_tac >>
  `expr_vv_sim_mem unit.cu_context func cenv'
    (initial_evaluation_context am.sources am.layouts tx NONE) ret e es` by fs[] >>
  drule_all external_frame_ret_widened_call_mem >> simp[]
QED
