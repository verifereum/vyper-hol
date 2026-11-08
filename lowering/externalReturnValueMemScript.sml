(* A valued return of the external frame, once the value is in place,
   runs memory-safely to an exit, for a value laid out at its expression
   type: the lowering's value type is the expression's own, or both are
   bytestrings that fit.  The widened case is
   externalReturnWidenedCallMem's. *)
Theory externalReturnValueMem
Ancestors
  returnValueTyped externalReturnDirectMem externalReturnNormalizedMem
  externalReturnLeafMem externalNormalizePremises typedNormalizeRankMem
  externalReturnZeroLayout
  nonreentrantExit
  stmtSimDefs loweringPosts
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps valueEncodingProofs vyperInterpreter vyperContext
  venomExecSemantics venomState compileEnv e2eDefs supportedProgram
  compileVyper unitTransformDefs fragExec loweringHalt venomInst venomWf
  contextCodegenRel memSafeRun allocaFrontierBound o1PassContract ptrDiscipline
  vyperLoweringCorrect loweringRuntimeCorrect fragExecMem bodyMemoryDefs
  entryHaltMem loweringPtrCorrect bodySim bodySimMain moduleLowering
  stmtLowering vyperTypeSystem vyperState lowerDloadDefs

val _ = Parse.hide "body";

Theorem external_frame_ret_value_run_mem:
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
       ~t.vs_halted ==>
       ?fuel r. run_from fuel unit.cu_context func t = r /\ exit_result r /\
                mem_safe_run fuel unit.cu_context func t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `~is_word_type ret /\
    ~(is_bytestring_type (lowered_value_type cenv' e) /\ is_bytestring_type ret) /\
    lowered_value_type cenv' e <> ret`
  >- (qpat_x_assum `~is_word_type ret /\ _` strip_assume_tac >>
      drule_all external_frame_ret_value_normalized_run_mem >> simp[]) >>
  drule_all external_frame_ret_value_direct_run_mem >> simp[]
QED
