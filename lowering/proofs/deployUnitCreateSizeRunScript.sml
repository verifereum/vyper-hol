Theory deployUnitCreateSizeRun
Ancestors
  deployUnitExitSafe deployUnitExecution vyperInterpreter

(* Keep the CREATE-size exit clause on the same run as the selected
   constructor's source result. *)
Theorem deploy_unit_create_size_run:
  !marks tops runtime_bc am tx unit vs tail.
    deploy_unit_execution_correct_at marks tops runtime_bc am tx unit vs /\
    lowering_context_ok unit.cu_context /\
    deploy_storage_ok tops am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail) /\
    ~deploy_source_exempt tops
      (load_contract (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE,tops)] []) ==>
    ?fuel. exit_result (run_context fuel unit.cu_context vs) /\
      create_size_exit_ok unit.cu_context
        (load_contract (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE,tops)] [])
        (run_context fuel unit.cu_context vs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `deploy_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_unit_execution_correct_at_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `tail` mp_tac) >> gvs[])
  >- (qpat_x_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
        (qspec_then `tail` assume_tac) >> gvs[load_contract_def]) >>
  qpat_x_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
    (qspec_then `tail` assume_tac) >>
  drule_all deploy_unit_exit_arm_runs >> strip_tac >>
  qexists_tac `fuel` >> simp[load_contract_def]
QED
