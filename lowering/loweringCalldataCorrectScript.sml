(* S1 and S3 for every calldata: the call the calldata dispatches to
   (dispatched_vyper_call, including __default__ and noncanonical
   encodings), and the calldata that dispatches to nothing, which reverts
   with no data. *)
Theory loweringCalldataCorrect
Ancestors
  vyperCalldata calldataExact e2eDefs vyperLoweringCorrect loweringRuntimeCorrect
  loweringMemCorrect sourceUnitExecution runtimeEntryEndpoint
  dispatchedEntryEndpoint fallbackEntryEndpoint dispatchedEntryValueRevert
  dispatchedArgsBind gasShadowRunLowering gasShadowUnit supportedProgram

(* The call a contract makes of raw calldata: the external entry it
   dispatches to and the arguments it decodes (vyperCalldata), including the
   __default__ fallback and noncanonical encodings.  Nonreentrant functions
   and functions with default arguments stay excluded for now. *)
Definition dispatched_vyper_call_def:
  dispatched_vyper_call tops tx calldata ret <=>
    calldata_dispatch tops calldata = SOME (tx.function_name, tx.args) /\
    ?mut args body.
      vyperInterpreter$lookup_function NONE tx.function_name External tops =
        SOME (mut, F, args, [], ret, body)
End

(* S1 when the call value moves and the dispatched body starts. *)
Theorem lower_vyper_runtime_unit_body_joint_dispatched_with_shadow:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?shadow_unit marks.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      source_unit_execution_correct_with shadow_unit.cu_context marks
        tops ret am tx unit vs
Proof
  rpt strip_tac >>
  `calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
     SOME (tx.function_name, tx.args)` by fs[dispatched_vyper_call_def] >>
  `runtime_entry_endpoint tops rpolicy unit am tx vs es0 mut args ret fbody` by
    (Cases_on `tx.function_name = "__default__"`
     >- (drule_all dispatched_entry_endpoint_default >> simp[]) >>
     drule_all dispatched_entry_endpoint_selected >> simp[]) >>
  drule_all runtime_body_joint_from_start_with_shadow >> disch_then ACCEPT_TAC
QED

Theorem lower_vyper_runtime_unit_body_joint_dispatched:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?shadow_ctx func shadow_func marks.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      (((!tail.
           ~(source_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail) /\
             call_outcomes_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail))) /\
        ?(H : (bool # bytes32 # type_value) list # num list)
           leaf leaf_pg leaf_g leaf_tn finish.
          gas_origin_ptr_focus
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, gas_explicit_sites unit.cu_context shadow_ctx,
             unit.cu_context, func, [])
            ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>), FEMPTY, entry_taint)
            marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
       ?res am' rqs obs.
         (!tail. call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
            (res, am', rqs, obs)) /\
         ((source_exempt tops (res, am', rqs) /\
           ?(H : (bool # bytes32 # type_value) list # num list)
              leaf leaf_pg leaf_g leaf_tn finish.
             gas_origin_ptr_focus
               (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
                0, gas_explicit_sites unit.cu_context shadow_ctx,
                unit.cu_context, func, [])
               ((vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0 |>), FEMPTY, entry_taint)
               marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) \/
          (?r. exit_result r /\
             storage_trace_domain
               (initial_evaluation_context am.sources am.layouts tx NONE)
               (initial_state am []) obs /\
             gas_origin_path T
               (gas_explicit_sites unit.cu_context shadow_ctx)
               unit.cu_context func
               (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |>) marks r /\
             !H. valid_horizon
                   (initial_evaluation_context am.sources am.layouts tx NONE)
                   (initial_state am []) H obs ==>
               external_call_result_rel H tops ret tx (res, am', rqs) r /\
               (!fuel. ptr_safe_blocks
                 (cx_dead H
                   (initial_evaluation_context am.sources am.layouts tx NONE))
                 0 fuel unit.cu_context func [] FEMPTY entry_taint
                 (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                             vs_inst_idx := 0 |>)))))
Proof
  rpt strip_tac >>
  drule_all lower_vyper_runtime_unit_body_joint_dispatched_with_shadow >>
  disch_then (qx_choosel_then [`shadow_unit`, `marks`] strip_assume_tac) >>
  qpat_x_assum `source_unit_execution_correct_with _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_with_def]) >>
  qexistsl_tac [`shadow_unit.cu_context`, `func`, `shadow_func`, `marks`] >> simp[]
QED

(* S1 *)
Theorem lower_vyper_runtime_unit_correct_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes)
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  rpt strip_tac >>
  `?mut args fbody.
     vyperInterpreter$lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody)` by
    (fs[dispatched_vyper_call_def] >> metis_tac[]) >>
  `calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
     SOME (tx.function_name, tx.args)` by fs[dispatched_vyper_call_def] >>
  drule_all dispatched_vyper_call_bind >> strip_tac >>
  Cases_on `send_call_value mut
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am [env] with
                 <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all lower_vyper_runtime_unit_body_joint_dispatched >> strip_tac >>
      simp[source_unit_execution_correct_def,
           source_unit_execution_correct_at_def] >>
      qexists_tac `marks` >>
      qexistsl_tac [`shadow_ctx`, `func`, `shadow_func`] >> simp[]) >>
  irule external_entry_value_revert_dispatched >> metis_tac[]
QED

(* The compiled shadow is chosen before the execution environment and state. *)
Theorem lower_vyper_runtime_unit_correct_dispatched_with:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops ==>
    ?shadow_ctx.
      gas_shadow_context unit.cu_context shadow_ctx /\
      !am tx ret vs.
        source_typing_ok tops am tx /\
        source_deployment_rel tops am tx /\
        dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
        initial_venom_state_rel tops am tx vs /\
        outcomes_accounts_typed (SOME vs.vs_outcomes) ==>
        ?marks. source_unit_execution_correct_with shadow_ctx marks
          tops ret am tx unit vs
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  `~EXISTS external_has_defaults q` by
    (drule supported_program_no_external_defaults >> simp[]) >>
  drule_all runtime_gas_shadow_unit_exists >> strip_tac >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
  qexists_tac `shadow_unit.cu_context` >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `?mut args fbody.
     vyperInterpreter$lookup_function NONE tx.function_name External tops =
       SOME (mut, F, args, [], ret, fbody)` by
    (fs[dispatched_vyper_call_def] >> metis_tac[]) >>
  `calldata_dispatch tops vs.vs_call_ctx.cc_calldata =
     SOME (tx.function_name, tx.args)` by fs[dispatched_vyper_call_def] >>
  drule_all dispatched_vyper_call_bind >> strip_tac >>
  Cases_on `send_call_value mut
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am [env] with
                 <| outcomes := SOME vs.vs_outcomes; requests := [] |>)` >>
  rename1 `_ = (sres, es0)` >> Cases_on `sres`
  >- (rename1 `INL u` >> Cases_on `u` >>
      drule_all lower_vyper_runtime_unit_body_joint_dispatched_with_shadow >>
      strip_tac >> gvs[] >> qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
  qexists_tac `[]` >>
  irule external_entry_value_revert_dispatched_with >> metis_tac[]
QED

(* S1, calldata that dispatches to nothing: no fallback, a short head, or a
   failed decode.  The entry reverts with empty returndata before any
   function body runs. *)
Theorem lower_vyper_runtime_unit_reverts:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs
    ==>
    ?fuel s. run_context fuel unit.cu_context vs = Abort Revert_abort s /\
             s.vs_returndata = []
Proof
  (* HELD ADMISSION SEQ-4940: S1 revert on a NONE dispatch; needs the selector-miss and decode-failure entry runs *)
  cheat
QED

(* S3 *)
Theorem lower_vyper_runtime_unit_memory_ok_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    ~ctx_has_dalloca unit.cu_context
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        taint_within
          (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
          unit.cu_context vs
Proof
  (* HELD ADMISSION SEQ-4941: S3 twin of SEQ-4939 *)
  cheat
QED

(* S3, calldata that dispatches to nothing. *)
Theorem lower_vyper_runtime_unit_reverts_memory_ok:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        ?D. dead_wf D /\ taint_within D unit.cu_context vs /\
        (code_layout_valid vs ==> mem_inv dload_offset_ok unit.cu_context vs)
Proof
  (* HELD ADMISSION SEQ-4942: S3 twin of SEQ-4940 *)
  cheat
QED

(* DLOAD offsets stay within the data section, for every dispatched call. *)
Theorem lower_vyper_runtime_unit_dload_offset_ok_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    code_layout_valid vs /\
    (!marks. ~source_exempt tops
       (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx))
    ==> mem_inv dload_offset_ok unit.cu_context vs
Proof
  (* HELD ADMISSION SEQ-4943: dispatched form of the proved canonical dload_offset_ok *)
  cheat
QED
