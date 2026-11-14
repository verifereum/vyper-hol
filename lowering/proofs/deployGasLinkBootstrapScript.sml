(* Bootstrap the deployment gas mask from the raw witness's exit arm. *)
Theory deployGasLinkBootstrap
Ancestors
  e2eDeployAtMarks deployUnitExitSafe ctorDeployMemoryFrontier
  ctorDeployShape ctorDeployDead o1PipelineCorrect o1PassContract
  fragGasOrigin fragGasOriginPtr gasSummary vyperStorageFootprint
  gasMaskProjection fragGasOriginPtrSafeUpto fragGasOriginFocusEvents
  deployUnitExecution ctorDeployImmBudget e2eDefs e2eDeployDefs ctorDeployDefs
  e2eEntry vyperInterpreter gasEvents dftContractGas
  acceptedContextPhi fragExec entryDispatchMem

(* The all-dead witness's exit arm bootstraps the output invariant before
   selecting a gas mask or a source filling. *)
Theorem deploy_unit_exit_pipeline:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es
   vs func sites marks src obs result.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    (!D. dead_wf D ==>
       raw_unit_memory_ok dunit.cu_context vs /\
       ptr_discipline (imm_len tops) dunit.cu_context vs /\
       taint_within D dunit.cu_context vs /\
       mem_inv dload_offset_ok dunit.cu_context vs /\
       mem_inv dload_headroom_ok dunit.cu_context vs ==>
       ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
         (deploy_entry_state prog cplan tops es) /\
       o1_lowered_inv dout.po_unit.cu_context
         (deploy_entry_state prog cplan tops es)) /\
    lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__deploy" /\
    exit_result result /\
    storage_trace_domain (deploy_evaluation_context tops am tx)
      (initial_state am []) obs /\
    gas_origin_path T sites dunit.cu_context func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0 |>) marks result /\
    (!H. valid_horizon (deploy_evaluation_context tops am tx)
           (initial_state am []) H obs ==>
       deploy_venom_result_rel H tops runtime_bc tx src result /\
       !fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
         (imm_len tops) fuel dunit.cu_context func [] FEMPTY entry_taint
         (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                     vs_inst_idx := 0 |>)) ==>
    o1_lowered_inv dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es) /\
    ?fuel. terminates (run_context fuel dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_entry_facts >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule_all deploy_unit_exit_arm_runs >> strip_tac >>
  drule_all deploy_selected_memory >> strip_tac >>
  qabbrev_tac `H = storage_trace_horizon obs` >>
  `ctx_sim (deploy_dead H tops runtime_bc am tx) dunit.cu_context
     dout.po_unit.cu_context vs (deploy_entry_state prog cplan tops es) /\
   o1_lowered_inv dout.po_unit.cu_context
     (deploy_entry_state prog cplan tops es)` by
    (qpat_x_assum `!D. dead_wf D ==> _`
       (qspec_then `deploy_dead H tops runtime_bc am tx` mp_tac) >>
     impl_tac >- simp[deploy_dead_wf] >>
     impl_tac >- fs[Abbr `H`] >> simp[]) >>
  simp[] >>
  `terminates (run_context fuel dunit.cu_context vs)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  metis_tac[ctx_sim_def, dead_result_rel_terminates]
QED


(* Focus certificates can select no more observations than the fixed mask.
   The spare reading prevents a focus beyond the end of that mask. *)
Theorem deploy_focus_mask_prefix[local]:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  LENGTH vs.vs_gas_readings = LENGTH sites + 1 /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!D n fuel.
     dead_wf D /\ o1_safe_upto D (imm_len tops) n dunit.cu_context vs /\
     n <= LENGTH (gas_events_blocks fuel dunit.cu_context func
       (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0|>)) ==>
     ?extra. sites = TAKE n (gas_events_blocks fuel dunit.cu_context func
       (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0|>)) ++ extra) /\
  gas_origin_ptr_focus
    (deploy_dead H tops runtime_bc am tx, imm_len tops,
     gas_explicit_sites dunit.cu_context shadow_ctx, dunit.cu_context, func, [])
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
               vs_inst_idx := 0|>, FEMPTY, entry_taint)
    marks (leaf, leaf_pg, leaf_g, leaf_tn, stop_state) ==>
  ?rest. MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx)
    sites = marks ++ rest
Proof
  strip_tac >>
  drule_all deploy_entry_facts >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule_all lowered_unit_entry_facts >> strip_tac >>
  `ptr_ok_check dunit.cu_context` by fs[vyperCompilerTheory.lowering_context_ok_def] >>
  drule_all ptrOkCheckTheory.ptr_ok_check_sound >> strip_tac >>
  `fmp_free_ctx dunit.cu_context` by metis_tac[o1PipelineComposeTheory.source_fmp_free] >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `mem_inv dload_headroom_ok dunit.cu_context vs` by
    (irule lowered_unit_dload_headroom_ok_from >> metis_tac[]) >>
  `imm_len tops <= vs.vs_alloca_next` by simp[] >>
  drule_all gas_origin_ptr_focus_o1_safe_upto >> strip_tac >>
  drule gas_origin_ptr_focus_origin >> strip_tac >>
  drule gas_origin_focus_entry_events >> simp[] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `MAP project events = marks ++ extra` >>
  `LENGTH marks <= LENGTH events` by
    (qpat_x_assum `MAP _ events = _` (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qabbrev_tac `n = MIN (LENGTH marks) (LENGTH vs.vs_gas_readings)` >>
  `n <= LENGTH events` by simp[Abbr `n`] >>
  `dead_wf (deploy_dead H tops runtime_bc am tx)` by simp[deploy_dead_wf] >>
  qpat_x_assum `!D n fuel. _`
    (qspecl_then [`deploy_dead H tops runtime_bc am tx`, `n`, `fuel`] mp_tac) >>
  impl_tac >- simp[Abbr `events`] >>
  disch_then (qx_choose_then `site_tail` assume_tac) >>
  `n <= LENGTH sites` by
    (qpat_x_assum `sites = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[Abbr `events`, listTheory.LENGTH_TAKE] >> decide_tac) >>
  `n = LENGTH marks` by (fs[Abbr `n`, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  qexists_tac `MAP project site_tail` >>
  qpat_x_assum `sites = _` SUBST1_TAC >>
  simp[GSYM (Abbr `events`), listTheory.MAP_APPEND, listTheory.MAP_TAKE] >>
  qpat_x_assum `MAP project events = _` mp_tac >>
  disch_then (mp_tac o Q.AP_TERM `TAKE (LENGTH marks)`) >>
  simp[rich_listTheory.TAKE_LENGTH_APPEND]
QED

(* The full mask applies to exit certificates without a storage guard. *)
Theorem deploy_exit_mask_prefix[local]:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!D. (?fr. terminates (run_context fr dunit.cu_context vs)) /\
     dead_wf D /\ raw_unit_memory_ok dunit.cu_context vs /\
     ptr_discipline (imm_len tops) dunit.cu_context vs /\
     taint_within D dunit.cu_context vs /\
     mem_inv dload_offset_ok dunit.cu_context vs /\
     mem_inv dload_headroom_ok dunit.cu_context vs ==>
     (!fr. terminates (run_context fr dunit.cu_context vs) ==>
       ?extra. sites = gas_events_blocks fr dunit.cu_context func
         (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0|>) ++ extra) /\
     ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
       (deploy_entry_state prog cplan tops es)) /\
  exit_result result /\
  storage_trace_domain (deploy_evaluation_context tops am tx)
    (initial_state am []) obs /\
  gas_origin_path T (gas_explicit_sites dunit.cu_context shadow_ctx)
    dunit.cu_context func
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
               vs_inst_idx := 0|>) marks result /\
  (!H. valid_horizon (deploy_evaluation_context tops am tx)
         (initial_state am []) H obs ==>
     deploy_venom_result_rel H tops runtime_bc tx src result /\
     !fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
       (imm_len tops) fuel dunit.cu_context func [] FEMPTY entry_taint
       (vs with <|vs_prev_bb := NONE; vs_current_bb := "__deploy";
                  vs_inst_idx := 0|>)) ==>
  (?rest. MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx)
     sites = marks ++ rest) /\
  (!D. dead_wf D ==> raw_unit_memory_ok dunit.cu_context vs /\
     ptr_discipline (imm_len tops) dunit.cu_context vs /\
     taint_within D dunit.cu_context vs /\
     mem_inv dload_offset_ok dunit.cu_context vs /\
     mem_inv dload_headroom_ok dunit.cu_context vs ==>
     ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
       (deploy_entry_state prog cplan tops es))
Proof
  strip_tac >>
  drule_all deploy_entry_facts >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule_all deploy_unit_exit_arm_runs >> strip_tac >>
  `?fr. terminates (run_context fr dunit.cu_context vs)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  reverse conj_tac >- metis_tac[] >>
  drule_all deploy_selected_memory >> strip_tac >>
  qpat_x_assum `!D. (?fr. _) /\ _ ==> _`
    (qspec_then `deploy_dead (storage_trace_horizon obs) tops runtime_bc am tx` mp_tac) >>
  impl_tac >- (simp[deploy_dead_wf] >> metis_tac[]) >> strip_tac >>
  drule_all gas_origin_path_events >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_from f dunit.cu_context func s0 = result` >>
  `phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lowering_context_ok_block_phi] >>
  `s0 with vs_inst_idx := 0 = s0` by simp[Abbr `s0`] >>
  `run_context (SUC f) dunit.cu_context vs = result` by
    metis_tac[Abbr `s0`, run_blocks_run_from_no_phi, run_context_run_blocks] >>
  `terminates (run_context (SUC f) dunit.cu_context vs)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  qpat_x_assum `!fr. terminates _ ==> _` drule >> strip_tac >>
  qexists_tac `MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx) extra` >>
  simp[listTheory.MAP_APPEND] >>
  simp[Once gas_events_blocks_def, eval_phis_no_phi, Abbr `s0`]
QED

(* The target mask-entry bridge remains a premise. Each selected raw
   filling has one spare zero before its certificate chooses marks. The
   prefix at MIN (LENGTH marks) (LENGTH sites + 1) then fits in sites,
   forcing it to cover all selected marks. *)
Theorem deploy_pipeline_gas_link_from_mask_entry:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    (?shadow_ctx. !vs.
       gas_variant vs (deploy_entry_state prog cplan tops es) ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am tx dunit vs) /\
    dft_blocks_gas_prefix /\
    o1_lowered_inv dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es) /\
    (?fuel fn lbl.
       dout.po_unit.cu_context.ctx_entry = SOME "__deploy" /\
       lookup_function "__deploy" dout.po_unit.cu_context.ctx_functions = SOME fn /\
       fn_entry_label fn = SOME lbl /\
       terminates (run_context fuel dout.po_unit.cu_context
         (deploy_entry_state prog cplan tops es)) /\
       gas_count_blocks fuel dout.po_unit.cu_context fn
         ((deploy_entry_state prog cplan tops es) with
           <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) <=
         LENGTH (deploy_entry_state prog cplan tops es).vs_gas_readings) ==>
    gas_readings_rel (gas_readings es)
      (\gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs ==>
            ?vs marks tail.
              gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
              gas_variant vs (deploy_entry_state prog cplan tops es) /\
              (~deploy_source_exempt tops
                 (load_contract (SOME vs.vs_outcomes)
                   (gas_explicit marks vs.vs_gas_readings ++ tail)
                   am tx [(NONE, tops)] []) ==>
               !D. dead_wf D ==>
                 raw_unit_memory_ok dunit.cu_context vs /\
                 ptr_discipline (imm_len tops) dunit.cu_context vs /\
                 taint_within D dunit.cu_context vs /\
                 mem_inv dload_offset_ok dunit.cu_context vs /\
                 mem_inv dload_headroom_ok dunit.cu_context vs ==>
                 ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
                   (deploy_entry_state prog cplan tops es) /\
                 o1_lowered_inv dout.po_unit.cu_context
                   (deploy_entry_state prog cplan tops es)) /\
              deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vs) T

Proof
  rpt gen_tac >> strip_tac >>
  `gas_variant (deploy_entry_state prog cplan tops es)
     (deploy_entry_state prog cplan tops es)` by simp[gas_variant_def] >>
  drule_all deploy_entry_facts >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all ctorDeployDefsReachTheory.deploy_unit_defs_reach_uses >> strip_tac >>
  `o1_pipeline rpolicy dunit = SOME dout` by fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_gas_mask_prefix >>
  disch_then (qx_choosel_then [`raw_slots`, `sites`, `unused`] strip_assume_tac) >>
  qabbrev_tac `project = MAP (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx) sites` >>
  `LENGTH project = LENGTH raw_slots` by simp[Abbr `project`] >>
  drule gas_mask_recorded_partition >> strip_tac >>
  rewrite_tac[gas_readings_rel_def] >>
  qexistsl [`MAP SND (FILTER FST (ZIP (project, raw_slots)))`,
    `MAP THE (FILTER IS_SOME (MAP SND (FILTER ($~ o FST) (ZIP (project, raw_slots))))) ++ unused`] >>
  conj_tac
  >- (simp[listTheory.APPEND_ASSOC] >>
      irule sortingTheory.PERM_TRANS >>
      qexists_tac `MAP THE (FILTER IS_SOME raw_slots) ++ unused` >>
      simp[] >> conj_tac
      >- (rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[sortingTheory.PERM_APPEND_IFF]) >>
      fs[deploy_entry_state_def, e2eEntryTheory.entry_venom_state_def]) >>
  rpt gen_tac >> strip_tac >>
  drule_all gas_mask_filling_extension >> strip_tac >>
  qabbrev_tac `vs = deploy_entry_state prog cplan tops es with vs_gas_readings := raw ++ [0w]` >>
  `gas_variant vs (deploy_entry_state prog cplan tops es)` by simp[Abbr `vs`, gas_variant_def] >>
  qpat_x_assum `!vs. gas_variant _ _ ==> _` drule >> strip_tac >>
  `LENGTH vs.vs_gas_readings = LENGTH sites + 1` by
    (imp_res_tac listTheory.LIST_REL_LENGTH >> simp[Abbr `vs`]) >>
  `vs.vs_outcomes = MAP SND (call_trace es)` by simp[Abbr `vs`] >>
  `deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vs` by
    metis_tac[deploy_unit_execution_correct_at_with] >>
  qpat_x_assum `!gobs tail D. _` (qspecl_then [`raw`, `[0w]`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `dft_blocks_gas_prefix ==> _` (mp_tac o UNDISCH) >>
  disch_then (qspecl_then [`raw`, `[0w]`] mp_tac) >>
  simp[] >> strip_tac >>
  `?rest. project = marks ++ rest` by
    (qpat_assum `deploy_unit_execution_correct_with _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[deploy_unit_execution_correct_with_def] >> strip_tac
     >- (metis_tac[deploy_focus_mask_prefix])
     >- (metis_tac[deploy_focus_mask_prefix]) >>
     qpat_x_assum `!D. (?fr. _) /\ _ ==> _` mp_tac >>
     simp[] >> strip_tac >>
     drule_all deploy_exit_mask_prefix >> simp[GSYM (Abbr `project`)]) >>
  `gobs = gas_explicit marks vs.vs_gas_readings ++
      gas_explicit rest (DROP (LENGTH marks) vs.vs_gas_readings)` by
    (qpat_x_assum `!tail. gas_explicit project _ = _` (qspec_then `[0w]` mp_tac) >>
     simp[Abbr `vs`, gas_explicit_append]) >>
  simp[] >> strip_tac >>
  qexistsl [`vs`, `marks`, `gas_explicit rest (DROP (LENGTH marks) vs.vs_gas_readings) ++ tail`] >>
  simp[listTheory.APPEND_ASSOC] >>
  qpat_assum `deploy_unit_execution_correct_with _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[deploy_unit_execution_correct_with_def] >> strip_tac
  >- metis_tac[listTheory.APPEND_ASSOC]
  >- (qpat_x_assum `!tail. load_contract_trace _ _ _ _ _ _ = _`
        (qspec_then `gas_explicit rest (DROP (LENGTH marks) vs.vs_gas_readings) ++ tail` mp_tac) >>
      simp[GSYM load_contract_def, listTheory.APPEND_ASSOC] >>
      metis_tac[load_contract_def, pairTheory.FST]) >>
  `?fr. terminates (run_context fr dunit.cu_context vs)` by
    (drule_all deploy_entry_facts >> strip_tac >>
     drule_all deploy_unit_run_entry >> strip_tac >>
     drule o1_source_unit_ok_no_dalloca >> strip_tac >>
     drule_all deploy_unit_exit_arm_runs >> strip_tac >>
     metis_tac[deploy_venom_result_rel_terminates]) >>
  rpt strip_tac >>
  qpat_x_assum `!D. (?fr. _) /\ _ ==> _` (qspec_then `D` mp_tac) >>
  impl_tac >- metis_tac[] >> simp[]
QED
