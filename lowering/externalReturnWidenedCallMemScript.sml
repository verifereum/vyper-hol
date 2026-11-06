(* An incompatible internal-call layout yields the counted return contract
   through the actual value-view expression prefix, not an arbitrary
   expression postcondition endpoint. *)
Theory externalReturnWidenedCallMem
Ancestors
  externalReturnLeafMem externalNormalizePremises typedNormalizeRankMem
  nonreentrantExit internalReturnMetadata incompatibleReturnLayout returnLocatedMismatchMem
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
    !cenv' env lctx e es d RetQ.
       same_frame cenv cenv' /\
       ~(lowered_value_type cenv' e = expr_type e \/
        is_bytestring_type (expr_type e) /\
        is_bytestring_type (lowered_value_type cenv' e) /\
        arg_type_fits (lowered_value_type cenv' e) (expr_type e)) /\
       expr_sim_inv cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) env es /\
       IS_SOME (type_stmt env ret (Return (SOME e))) /\
       expr_vv_sim_mem unit.cu_context func cenv'
         (initial_evaluation_context am.sources am.layouts tx NONE) ret e es ==>
       stmt_frag_mem d unit.cu_context func
         (initial_evaluation_context am.sources am.layouts tx NONE) lctx RetQ cenv'
         (stmt_env cenv' lctx ret (Return (SOME e)))
         (eval_stmt (initial_evaluation_context am.sources am.layouts tx NONE)
           (Return (SOME e))) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all external_package_frame_internal_maps >> strip_tac >>
  irule return_located_mismatch_mem >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule incompatible_return_layout_located >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
