(* One selected raw-unit execution fixes its gas marks and source trace
   before every finite storage horizon. *)
Theory sourceUnitExecution
Ancestors
  e2eDefs gasSummary gasExplicitSites fragGasOrigin ptrSafeRun
  loweringStateRelDefs ptrDiscipline unitTransformDefs

(* The dead bytes the body's run may leave taint in: those storage_dead
   gives in the running contract's storage and transient storage, as
   external_call_dead does for the source call that cx is the context of.
   The return data may hold no taint. *)
Definition cx_dead_def:
  cx_dead H cx =
    <| d_stor := (\a st. if a = cx.txn.target
                         then {(k,b) | storage_dead H F st (w2n k) b}
                         else {});
       d_trans := (\a st. if a = cx.txn.target
                          then {(k,b) | storage_dead H T st (w2n k) b}
                          else {});
       d_imm := K {}; d_ret := K {} |>
End

(* Exact selected-run certificate from UNIT-H-r4; fixed Boolean marks. *)
Definition source_unit_execution_correct_at_def:
  source_unit_execution_correct_at marks tops ret am tx unit vs <=>
    ?shadow_ctx func shadow_func.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      ((!tail.
          ~(source_storage_ok am tx vs.vs_outcomes
              (gas_explicit marks vs.vs_gas_readings ++ tail) /\
            call_outcomes_storage_ok am tx vs.vs_outcomes
              (gas_explicit marks vs.vs_gas_readings ++ tail))) \/
       ?res am' rqs obs.
         (!tail. call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
            (res, am', rqs, obs)) /\
         ((source_exempt tops (res, am', rqs) /\
           ?leaf finish.
             gas_origin_focus T
               (gas_explicit_sites unit.cu_context shadow_ctx)
               (unit.cu_context, func)
               (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                           vs_inst_idx := 0 |>) marks (leaf, finish)) \/
          (~source_exempt tops (res, am', rqs) /\
           ?r. exit_result r /\
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
End

Definition source_unit_execution_correct_def:
  source_unit_execution_correct tops ret am tx unit vs <=>
    ?marks. source_unit_execution_correct_at marks tops ret am tx unit vs
End
