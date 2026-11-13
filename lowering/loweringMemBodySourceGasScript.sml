(* Source result admissibility is independent of the gas readings. *)
Theory loweringMemBodySourceGas
Ancestors
  externalBodySourceOk stmtSimDefs gasContext list
  e2eDefs supportedProgram vyperInterpreter vyperState vyperContext venomState

Theorem external_body_source_ok_gas_mem:
  !tops am tx ret vs mut args fbody env es0.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    gas_admissible
      (eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
         fbody)
      (stmt_res_ok NoLoop) es0
Proof
  rpt strip_tac >> rw[gas_admissible_def] >>
  drule_all external_body_source_ok >> simp[]
QED
