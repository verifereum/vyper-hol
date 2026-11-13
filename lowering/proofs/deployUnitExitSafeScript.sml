(*
 * The exit arm of one selected deployment-unit execution gives the runs
 * from "__deploy" that the deploy memory bridges take
 * (ctorDeployMemoryFrontier's lowered_unit_raw_memory_ok_from,
 * lowered_unit_dload_offset_ok, lowered_unit_dload_headroom_ok_from and
 * lowered_unit_ptr_taint), and the unit's result at the observed horizon:
 * the deployment twin of sourceUnitExitSafe.  The certificate fixes the
 * source run at every tail of gas readings past the marked ones, so the
 * facts hold at each such filling.
 *
 * At the certificate's own fixed marks, the storage guard rules out its
 * bad-storage arm and ~deploy_source_exempt its exempt arm.  On the exit
 * arm, gas_origin_path T ends in an exit, so the run from "__deploy" is
 * memory-safe at every fuel and is the unit's run; storage_trace_domain
 * makes the observed horizon valid, at which the arm gives the
 * pointer-safe run and the result relation.
 *
 * TOP-LEVEL:
 *   deploy_unit_exit_safe_runs -- the entry's memory-safe run, its
 *     pointer-safe run and the unit's result, at the observed horizon
 *)
Theory deployUnitExitSafe
Ancestors
  deployUnitExecution e2eDeployDefs ctorDeployDefs vyperStorageFootprint
  vyperInterpreter fragGasOrigin fragGasMode fragGasPathMem fragExecMem
  fragExec memSafeRun entryDispatchMem acceptedContextPhi

(* The exit arm already makes its observed horizon valid.  This bridge
   therefore needs no selected filling's storage guard. *)
Theorem deploy_unit_exit_arm_runs:
  !tops runtime_bc am tx unit vs func sites marks src obs r.
    lowering_context_ok unit.cu_context /\ ~ctx_has_dalloca unit.cu_context /\
    unit.cu_context.ctx_entry = SOME "__deploy" /\
    lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    exit_result r /\
    storage_trace_domain (deploy_evaluation_context tops am tx)
      (initial_state am []) obs /\
    gas_origin_path T sites unit.cu_context func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0 |>) marks r /\
    (!H. valid_horizon (deploy_evaluation_context tops am tx)
           (initial_state am []) H obs ==>
      deploy_venom_result_rel H tops runtime_bc tx src r /\
      (!fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
        (imm_len tops) fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>))) ==>
    ?fuel.
      (!fuel. mem_safe_blocks fuel unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>)) /\
      (!fuel. ptr_safe_blocks
        (deploy_dead (storage_trace_horizon obs) tops runtime_bc am tx)
        (imm_len tops) fuel unit.cu_context func [] FEMPTY entry_taint
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>)) /\
      deploy_venom_result_rel (storage_trace_horizon obs) tops runtime_bc tx src
        (run_context fuel unit.cu_context vs) /\
      run_context fuel unit.cu_context vs = r
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `s0 = vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                               vs_inst_idx := 0 |>` >>
  `deploy_venom_result_rel (storage_trace_horizon obs) tops runtime_bc tx src r /\
   !fuel. ptr_safe_blocks
     (deploy_dead (storage_trace_horizon obs) tops runtime_bc am tx)
     (imm_len tops) fuel unit.cu_context func [] FEMPTY entry_taint s0` by
    (first_x_assum (qspec_then `storage_trace_horizon obs` mp_tac) >>
     fs[storage_trace_domain_def]) >>
  `?f. run_from f unit.cu_context func s0 = r /\
       mem_safe_run f unit.cu_context func s0` by
    (drule gas_origin_path_erase >> simp[gas_marked_path_def] >>
     strip_tac >> drule gas_path_mem_exec >> strip_tac >>
     gvs[exit_result_def] >> metis_tac[]) >>
  `!m. mem_safe_run m unit.cu_context func s0` by
    (qspecl_then [`f`, `unit.cu_context`, `func`, `s0`] mp_tac
       mem_safe_run_all_fuel >>
     impl_tac >- metis_tac[exit_result_not_error] >> simp[]) >>
  `s0.vs_current_bb = "__deploy"` by simp[Abbr `s0`] >>
  `?bb. lookup_block "__deploy" func.fn_blocks = SOME bb` by
    (Cases_on `lookup_block "__deploy" func.fn_blocks` >> simp[] >>
     qpat_x_assum `run_from _ _ _ _ = r` mp_tac >>
     simp[run_from_def] >> strip_tac >> gvs[exit_result_def]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lowering_context_ok_block_phi] >>
  `s0 with vs_inst_idx := 0 = s0` by simp[Abbr `s0`] >>
  `run_context (SUC f) unit.cu_context vs =
     run_blocks (SUC f) unit.cu_context func s0` by
    (qspecl_then [`SUC f`, `unit.cu_context`, `vs`, `"__deploy"`, `func`,
                  `"__deploy"`] mp_tac run_context_run_blocks >>
     simp[Abbr `s0`]) >>
  `run_blocks (SUC f) unit.cu_context func s0 = r` by
    (qspecl_then [`f`, `unit.cu_context`, `func`, `s0`, `bb`] mp_tac
       run_blocks_run_from_no_phi >> simp[]) >>
  qexists_tac `SUC f` >> simp[] >>
  irule mem_safe_blocks_no_phi >> asm_rewrite_tac[] >>
  qexists_tac `bb` >> simp[eval_phis_no_phi]
QED

Theorem deploy_unit_exit_safe_runs:
  !marks tops runtime_bc am tx unit vs tail.
    deploy_unit_execution_correct_at marks tops runtime_bc am tx unit vs /\
    lowering_context_ok unit.cu_context /\ ~ctx_has_dalloca unit.cu_context /\
    deploy_storage_ok tops am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail) /\
    ~deploy_source_exempt tops
      (load_contract (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE, tops)] [])
    ==>
    ?func fuel.
      lookup_function "__deploy" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__deploy" /\
      (!fuel. mem_safe_blocks fuel unit.cu_context func
         (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                     vs_inst_idx := 0 |>)) /\
      (!fuel. ptr_safe_blocks
         (deploy_dead
            (storage_trace_horizon
               (deploy_storage_trace (SOME vs.vs_outcomes)
                  (gas_explicit marks vs.vs_gas_readings ++ tail) am tx tops))
            tops runtime_bc am tx)
         (imm_len tops) fuel unit.cu_context func [] FEMPTY entry_taint
         (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                     vs_inst_idx := 0 |>)) /\
      deploy_venom_result_rel
        (storage_trace_horizon
           (deploy_storage_trace (SOME vs.vs_outcomes)
              (gas_explicit marks vs.vs_gas_readings ++ tail) am tx tops))
        tops runtime_bc tx
        (load_contract (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE, tops)] [])
        (run_context fuel unit.cu_context vs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `deploy_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [deploy_unit_execution_correct_at_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `tail` mp_tac) >> gvs[])
  >- (qpat_x_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
        (qspec_then `tail` assume_tac) >> gvs[load_contract_def]) >>
  qpat_x_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
    (qspec_then `tail` assume_tac) >> fs[] >>
  `load_contract (SOME vs.vs_outcomes) (gas_explicit marks vs.vs_gas_readings ++ tail)
     am tx [(NONE, tops)] [] = src /\
   deploy_storage_trace (SOME vs.vs_outcomes)
     (gas_explicit marks vs.vs_gas_readings ++ tail) am tx tops = obs` by
    simp[load_contract_def, deploy_storage_trace_def] >>
  ntac 2 (pop_assum SUBST1_TAC) >>
  drule_all deploy_unit_exit_arm_runs >> strip_tac >>
  qexists_tac `fuel` >> simp[]
QED
