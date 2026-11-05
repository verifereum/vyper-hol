(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalBodyFrame
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

(* ADMITTED (#637): at the start of the selected function's body, the
   premises of body_stmts_sim other than the frame's returns: the frame is
   the lowered program's (body_inv), the body is supported and typed at
   the return type in a type environment env_t of the parameters, which
   the compile env and the source state agree with and whose locals fit
   the allocation limit, and the external frame has no return PC and no
   lock. expr_sim_inv's storage-variable clause (each storage variable has
   its declared module type and no hash-map info) follows from body_inv
   and the single-module fact via body_inv_storage_var_types. *)
Theorem external_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
         (mut, F, lookup_raw_return_or_F (NONE : num option)
                     tx.function_name External tops,
          tx.function_name, args, [], ret, fbody)) =
      (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
       rt) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings fbody /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret fbody = SOME env' /\
      EVERY (stmt_exprs_ok cenv) fbody /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts fbody)
Proof
  cheat
QED

