(* Exact raw runtime execution and its result boundary for a linked unit. *)
Theory sourceUnitExecutionMods
Ancestors
  compileUnit e2eDefs e2eModsDefs finite_map sourceUnitExecution sourceExemptMods
  vyperContext vyperLoweringCorrect

Definition initial_venom_state_rel_mods_def:
  initial_venom_state_rel_mods mods am tx vs <=>
    value_transfer_ok tx am.accounts /\
    vs.vs_accounts = accounts_after_transfer tx am.accounts /\
    vs.vs_transient = am.tStorage /\ am.logs = [] /\ vs.vs_logs = [] /\
    tx_env_ok tx /\ venom_env_rel tx vs /\
    vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ vs.vs_memory = [] /\
    vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0 /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    vs.vs_returndata = [] /\ vs.vs_requests = [] /\
    vs.vs_pending_deletions = am.pending_deletions /\
    immutables_section_rel_mods mods (account_immutables am tx.target) vs.vs_data_section
End

Definition external_call_result_rel_mods_def:
  external_call_result_rel_mods H mods exps ret tx (res, am', rqs) vres <=>
    let src = ALOOKUP exps tx.function_name in
    let raw =
      case ALOOKUP mods src of
        NONE => F
      | SOME tops => lookup_raw_return_or_F src tx.function_name External tops in
    let tenv = type_env_all_modules mods in
    let events = build_event_info_mods tenv mods
          ((K NONE) : string -> (num # type list # bool list) option) in
    case (res, vres) of
      (INL v, Halt ss) =>
        (if raw then raw_return_bytes v = SOME ss.vs_returndata
         else return_bytes_mods mods ret v ss.vs_returndata) /\
        accounts_agree H tx.target am'.accounts
          (process_deletions ss.vs_pending_deletions ss.vs_accounts) /\
        transient_agree H tx.target am'.tStorage ss.vs_transient /\
        logs_correspond events tenv
          tx.target am'.logs ss.vs_logs /\
        LIST_REL (request_agree H tx.target) rqs ss.vs_requests
    | (INR HaltException, Halt ss) =>
        ss.vs_returndata = [] /\
        accounts_agree H tx.target am'.accounts
          (process_deletions ss.vs_pending_deletions ss.vs_accounts) /\
        transient_agree H tx.target am'.tStorage ss.vs_transient /\
        logs_correspond events tenv
          tx.target am'.logs ss.vs_logs /\
        LIST_REL (request_agree H tx.target) rqs ss.vs_requests
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error (RevertData _)), Abort Revert_abort _) => T
    | (INR (Error (RuntimeError m)), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt_mods mods e
    | _ => F
End

Definition source_unit_execution_correct_with_mods_def:
  source_unit_execution_correct_with_mods shadow_ctx marks mods exps ret am tx unit vs <=>
    ?func shadow_func.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      (((!tail.
           ~(call_storage_ok am tx vs.vs_outcomes
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
         ((source_exempt_mods mods (res, am', rqs) /\
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
               external_call_result_rel_mods H mods exps ret tx (res, am', rqs) r /\
               (!fuel. ptr_safe_blocks
                 (cx_dead H
                   (initial_evaluation_context am.sources am.layouts tx NONE))
                 0 fuel unit.cu_context func [] FEMPTY entry_taint
                 (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                             vs_inst_idx := 0 |>)))))
End

Theorem initial_venom_state_rel_mods_singleton:
  initial_venom_state_rel_mods [(NONE,tops)] am tx vs <=>
  initial_venom_state_rel tops am tx vs
Proof
  simp[initial_venom_state_rel_mods_def, initial_venom_state_rel_def,
       immutables_section_rel_mods_singleton]
QED

Theorem external_call_result_rel_mods_singleton:
  external_call_result_rel_mods H [(NONE,tops)] [] ret tx result vres <=>
  external_call_result_rel H tops ret tx result vres
Proof
  PairCases_on `result` >>
  simp[external_call_result_rel_mods_def, external_call_result_rel_def,
       build_event_info_mods_singleton, compiled_event_info_def,
       return_bytes_mods_singleton, unspecified_behaviour_exempt_mods_singleton,
       type_env_all_modules_def, type_env_def, FUNION_FEMPTY_2] >>
  BasicProvers.EVERY_CASE_TAC >> simp[]
QED

Theorem source_unit_execution_correct_with_mods_singleton:
  source_unit_execution_correct_with_mods shadow_ctx marks [(NONE,tops)] []
    ret am tx unit vs <=>
  source_unit_execution_correct_with shadow_ctx marks tops ret am tx unit vs
Proof
  simp[source_unit_execution_correct_with_mods_def,
       source_unit_execution_correct_with_def, source_exempt_mods_singleton,
       external_call_result_rel_mods_singleton]
QED
