(* The constructor prefix with memory: the run from the unit's entry, after
 * the payable check, the immutables region, the constructor arguments'
 * decode (DLOAD from the data section) and the lock, reaches the body start
 * sa in a state s0 related to the source's body start, with its allocation
 * history and the GAS readings still unread; and a memory-safe run from s0
 * makes the run from the entry memory-safe.  The constructor's frame has no
 * caller return buffer.
 * TOP-LEVEL: deploy_ctor_entry_run_mem.
 *)
Theory ctorDeployMemoryRunMemEntry
Ancestors
  ctorDeployLoweringDefs o1PassContract stmtSimDefs gasSummary memSafeRun
  allocaHistory venomInst ctorDeployShape o1PipelineCorrect ptrDiscipline
  exprLoweringProps compileVyper ctorDeployLoweringEntryBodyResources
  ctorDeployMemoryRunMemEntryLanding ctorDeployMemoryRunMemEntryProvenanceComplete
  ctorDeployMemoryRunMemEntryBoundary ctorDeployMemoryRunMemEntryTaskInputs
  ctorDeployLoweringFrame ctorDeployMemoryRunMemEntryResources
  ctorDeployMemoryRunMemEntrySourceWorld ctorDeployMemoryRunMemEntryTaskInitial
  ctorDeployMemoryRunMemEntryImmutableFrame ctorDeployDefs e2eDeployDefs e2eEntry venomState

(* The deployment unit has no DALLOCA (supported_program excludes it from
   the raw unit), so fmp_room, part of stmt_state_rel, holds vacuously at
   every state of each of its functions. *)
Theorem deploy_unit_fmp_room:
  !tops rpolicy runtime_bc dunit func ss.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    supported_program tops /\ supported_program_deploy tops /\
    MEM func dunit.cu_context.ctx_functions ==>
    fmp_room dunit.cu_context func ss
Proof
  rpt strip_tac >>
  drule_all lower_vyper_deploy_unit_source_unit_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >>
  rw[fmp_room_def, ctx_has_dalloca_def, listTheory.EXISTS_MEM,
     listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem ctor_path_mem_edge_code[local]:
  gas_path_mem_edge ctx fn s n (OK t) ==> t.vs_code = s.vs_code
Proof
  rw[fragGasPathMemTheory.gas_path_mem_edge_def] >>
  gvs[fragExecTheory.exit_result_def] >>
  imp_res_tac step_inst_ok_code_data >>
  imp_res_tac venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
  gvs[jump_to_def]
  >>~- ([`entered = _ with vs_vars := _`],
     qpat_x_assum `entered = _`
       (mp_tac o Q.AP_TERM `\u. u.vs_code`) >> simp[]) >>
  metis_tac[step_inst_ok_code_data, fragExecTheory.exit_result_def]
QED

Theorem ctor_path_mem_code[local]:
  gas_path_mem ctx fn s n (OK t) ==> t.vs_code = s.vs_code
Proof
  qsuff_tac `!ctx fn s n r. gas_path_mem ctx fn s n r ==>
    !t. r = OK t ==> t.vs_code = s.vs_code`
  >- metis_tac[] >>
  ho_match_mp_tac fragGasPathMemTheory.gas_path_mem_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      imp_res_tac ctor_path_mem_edge_code >> metis_tac[]) >>
  simp[fragExecTheory.exit_result_def] >>
  metis_tac[fragExecTheory.exit_result_def]
QED

Theorem deploy_ctor_entry_run_mem:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func
   mut am_c es0 fn lbl.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!marks. ~deploy_source_exempt tops
               (load_contract NONE (gas_explicit marks vs.vs_gas_readings) am tx
                  [(NONE, tops)] [])) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr, body, am_c, es0) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
    ==>
    cenv.ce_return_buf = NONE /\
    ?s0.
      stmt_state_rel dunit.cu_context func cenv
        (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      alloca_history func s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      ((!fuel. mem_safe_run fuel dunit.cu_context func s0) ==>
    !fuel. mem_safe_blocks fuel dunit.cu_context fn
             (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                         vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> strip_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >>
  drule_all ctor_checked_code_lookup_identity >> strip_tac >> gvs[] >>
  qpat_assum `deploy_ctor_code _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ctorDeployLoweringDefsTheory.deploy_ctor_code_def] >> strip_tac >>
  drule ctor_landing_package_target_invert >> strip_tac >>
  PairCases_on `cf` >>
  drule_all ctor_task_aligned_inputs >> strip_tac >> gvs[] >>
  drule ctor_landing_package_result_fields >> strip_tac >> gvs[] >>
  drule_all (SRULE [] ctor_task_register_world_provenance_complete) >>
  disch_then (qspec_then `ARB:instruction` strip_assume_tac) >>
  drule_all (SRULE [] ctor_landing_phase_metadata) >> strip_tac >>
  drule_all ctor_landing_source_scopes >> strip_tac >>
  drule_all ctor_task_entry_frontier >> strip_tac >>
  drule_all ctor_task_actual_resources >> strip_tac >>
  `!p. p < imm_len tops ==> mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 []` by
    (drule ctor_registered_immutable_byte_frame >>
     disch_then (qspec_then `imm_len tops` mp_tac) >>
     simp[] >> strip_tac >>
     `vs.vs_memory = []` by
       (qpat_x_assum `gas_variant _ _` mp_tac >>
        simp[gas_variant_def, deploy_entry_state_def, entry_venom_state_def,
             init_venom_state_def] >>
        disch_then (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >> simp[]) >>
     metis_tac[]) >>
  drule_all ctor_source_entry_world_projections >> strip_tac >>
  `actual.vs_code = vs.vs_code` by
    (qpat_assum `gas_path_mem _ _ (vs with <|vs_prev_bb := NONE;
       vs_current_bb := lbl; vs_inst_idx := 0|>) _ (OK actual)`
       (mp_tac o MATCH_MP ctor_path_mem_code) >> simp[]) >>
  `vs.vs_code = (deploy_evaluation_context tops am tx).txn.code` by
    (qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
     qpat_x_assum `gas_variant _ _` mp_tac >>
     simp[deploy_state_rel_def, gas_variant_def, deploy_entry_state_def,
          entry_venom_state_def, init_venom_state_def,
          deploy_evaluation_context_def,
          vyperInterpreterTheory.initial_evaluation_context_def] >>
     rpt strip_tac >> gvs[]) >>
  `actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_tx_ctx = vs.vs_tx_ctx /\
   actual.vs_block_ctx = vs.vs_block_ctx /\ actual.vs_outcomes = vs.vs_outcomes` by metis_tac[] >>
  drule_all ctor_source_candidate_context >>
  disch_then (qspec_then `es0` strip_assume_tac) >>
  `local_ptrs_rel fn (cenv1 with ce_ctor_exit_label := SOME exit_lbl) es0.scopes actual` by
    simp[ctor_landing_env_exit_label] >>
  `actual.vs_accounts = accounts_after_transfer tx am.accounts /\
   actual.vs_transient = am.tStorage /\ actual.vs_call_ctx.cc_address = tx.target /\
   actual.vs_logs = [] /\ actual.vs_requests = [] /\ actual.vs_pending_deletions = []` by
    (qpat_x_assum `abi_encoder_registered_effect _ _ _ _` mp_tac >>
     simp[abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
  drule_all ctor_task_landing_state_rel >> strip_tac >>
  drule ctor_checked_code_return_buf >> simp[] >> strip_tac >>
  `immutable_alloca_sep fn (cenv1 with ce_ctor_exit_label := SOME exit_lbl)
    (deploy_evaluation_context tops am tx) es0 actual` by
    (irule (cj 2 deploy_ctor_entry_immutable_resources) >>
     simp[ctor_landing_env_exit_label] >> metis_tac[deploy_source_ok_def]) >>
  qexists `actual` >> simp[] >>
  conj_tac
  >- (simp[stmt_state_rel_def] >>
      conj_tac
      >- (`supported_program tops /\ supported_program_deploy tops` by
            gvs[deploy_source_ok_def] >>
          drule_all deploy_unit_fmp_room >> simp[]) >>
      conj_tac
      >- (gvs[immutable_alloca_sep_def] >> metis_tac[]) >>
      conj_tac
      >- (drule ctorDeployMemoryRunMemEntryRegisterEnvTheory.ctor_register_constructor_env_fields >>
          strip_tac >> simp[] >>
          MATCH_MP_TAC (ctor_registered_immutable_base_zero |> SPEC_ALL
            |> Q.INST [`cap` |-> `imm_len tops`, `st` |-> `st1`]
            |> Q.GENL [`ce`, `actual`]) >>
          simp[] >> metis_tac[]) >>
      metis_tac[]) >>
  strip_tac >>
  drule_all (SRULE [] ctorDeployMemoryRunMemEntryTaskActualTheory.ctor_task_actual_phase_contracts) >>
  strip_tac >>
  `!bb. lookup_block actual.vs_current_bb fn.fn_blocks = SOME bb /\
        actual.vs_inst_idx = 0 ==> phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  qpat_assum `gas_path_mem _ _ (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
      vs_inst_idx := 0 |>) _ (OK actual)`
    (mp_tac o MATCH_MP ctorDeployMemoryRunMemEntryPathSafeTheory.ctor_checked_path_all_fuel) >>
  strip_tac >>
  `!fuel. mem_safe_run fuel dunit.cu_context fn
       (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by metis_tac[] >>
  drule_all ctorDeployMemoryRunMemEntryEntryPhiTheory.ctor_checked_task_entry_phi >> strip_tac >>
  irule ctorDeployMemoryRunMemEntryPathSafeTheory.ctor_checked_entry_blocks_bridge >> simp[] >>
  metis_tac[]
QED
