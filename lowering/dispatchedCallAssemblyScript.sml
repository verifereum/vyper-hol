(* Assemble dispatched calls once the selected entry reaches the body. *)
Theory dispatchedCallAssembly
Ancestors
  dispatchedArgsBind dispatchedEntryValueRevert fallbackEntryEndpoint
  loweringRuntimeCorrect gasShadowRunLowering loweringShapeProps
  gasShadowUnit sourceUnitExecution

Theorem dispatched_call_correct_from_value_success:
  !tops rpolicy unit shadow_unit am tx ret vs mut nr args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,[],ret,fbody) /\
    (!env es0. bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks
         tops ret am tx unit vs) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >> conj_asm2_tac
  >- (simp[source_unit_execution_correct_def,
           source_unit_execution_correct_at_with] >>
      qpat_x_assum `?marks. _` (qx_choose_then `marks` assume_tac) >>
      qexistsl_tac [`marks`, `shadow_unit.cu_context`] >> simp[]) >>
  drule_all dispatched_vyper_call_bind >>
  disch_then (qx_choose_then `env` assume_tac) >>
  namedCases_on `send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>)`
    ["res es0"] >>
  reverse (namedCases_on `res` ["u", "e"])
  >- (qexists_tac `[]` >>
      `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
        (Cases_on `classify_functions tops` >> PairCases_on `r` >>
         drule supported_program_no_external_defaults >> simp[] >> strip_tac >>
         drule_at (Pat `classify_functions _ = _`) runtime_gas_shadow_unit_exists >>
         disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
         simp[gas_shadow_unit_def]) >>
      drule_all external_entry_value_revert_dispatched_with_nr >> simp[]) >>
  Cases_on `u` >>
  qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]
QED

Theorem dispatched_call_correct_from_selected_endpoint:
  !tops rpolicy unit shadow_unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = SOME (tx.function_name, tx.args) /\
    initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    vyperInterpreter$lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    (!env es0. tx.function_name <> "__default__" /\
       bind_arguments (type_env tops) args tx.args = SOME env /\
       send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
         (initial_state am [env] with <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
         (INL (), es0) ==>
       runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody) ==>
    source_unit_execution_correct tops ret am tx unit vs /\
    ?marks. source_unit_execution_correct_with shadow_unit.cu_context marks tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >>
  irule dispatched_call_correct_from_value_success >>
  asm_rewrite_tac [] >> conj_tac
  >- (qexists_tac `rpolicy` >> asm_rewrite_tac []) >>
  qexistsl_tac [`args`, `fbody`, `mut`, `F`] >>
  asm_rewrite_tac [] >> rpt gen_tac >> strip_tac >>
  `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody` by
    (Cases_on `tx.function_name = "__default__"`
     >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
     qpat_x_assum `!env es0. _` (qspecl_then [`env`, `es0`] mp_tac) >> simp[]) >>
  drule_all runtime_body_joint_from_start_with_shadow >> simp[]
QED
