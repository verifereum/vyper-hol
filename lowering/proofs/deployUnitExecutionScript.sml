(* One selected deployment-unit execution fixes its gas marks and the
 * constructor run's trace before every finite storage horizon: the
 * deployment twin of sourceUnitExecution's source_unit_execution_correct.
 * TOP-LEVEL: deploy_unit_execution_correct_at, deploy_unit_execution_correct.
 *)
Theory deployUnitExecution
Ancestors
  sourceUnitExecution ctorDeployDefs e2eDeployDefs

(* At gas marks marks: either the constructor run's finite storage guard
   fails for every continuation of the selected readings, or the run's
   result and trace are fixed by them and the deployment unit either
   reaches the focused GAS read of an exempt source failure, or follows
   the selected gas path to an exit related to the source result, pointer
   safe, in every valid horizon of the run's trace. *)
Definition deploy_unit_execution_correct_at_def:
  deploy_unit_execution_correct_at marks tops runtime_bc am tx unit vs <=>
    ?shadow_ctx func shadow_func.
      unit.cu_context.ctx_entry = SOME "__deploy" /\
      lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__deploy" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      ((!tail. ~deploy_storage_ok tops am tx vs.vs_outcomes
                  (gas_explicit marks vs.vs_gas_readings ++ tail)) \/
       ?src obs.
         (!tail. load_contract_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings ++ tail) am tx
            [(NONE, tops)] [] = (src, obs)) /\
         ((deploy_source_exempt tops src /\
           ?leaf finish.
             gas_origin_focus T
               (gas_explicit_sites unit.cu_context shadow_ctx)
               (unit.cu_context, func)
               (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                           vs_inst_idx := 0 |>) marks (leaf, finish)) \/
          (?r. exit_result r /\
             gas_origin_path T
               (gas_explicit_sites unit.cu_context shadow_ctx)
               unit.cu_context func
               (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                           vs_inst_idx := 0 |>) marks r /\
             !H. valid_horizon (deploy_evaluation_context tops am tx)
                   (initial_state am []) H obs ==>
               deploy_venom_result_rel H tops runtime_bc tx src r /\
               (!fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
                 (imm_len tops) fuel unit.cu_context func [] FEMPTY entry_taint
                 (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                             vs_inst_idx := 0 |>)))))
End

Definition deploy_unit_execution_correct_def:
  deploy_unit_execution_correct tops runtime_bc am tx unit vs <=>
    ?marks. deploy_unit_execution_correct_at marks tops runtime_bc am tx unit vs
End
