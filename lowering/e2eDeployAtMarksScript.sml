(*
 * e2e_deploy_correct_from_gas_link: the deploy theorem from a link between the
 * frame's gas readings and selected raw entry states; the deployment twin of
 * e2eCallAtMarks.
 *
 * For every guarded filling of the frame's gas readings, the caller supplies
 * a raw deployment unit's entry state vs (a gas variant of the compiled
 * run's entry state) whose marked readings the filling extends, the S4
 * simulation facts on vs for every well-formed dead mask, and the
 * selected-run certificate at its marks.  At each such filling, the exit
 * arm gives the entry's memory- and pointer-safe runs at the run's own
 * storage horizon H (deployUnitExitSafe); the ctorDeployMemoryFrontier
 * bridges turn them into the S4 memory facts, which give ctx_sim at
 * deploy_dead H; codegen and the creation frame finish.
 *
 * TOP-LEVEL:
 *   e2e_deploy_correct_from_gas_link -- the deploy result relation at every
 *     filling, from the facts above
 *   gas_readings_rel_mono -- gas_readings_rel is monotone in its run
 *   gas_variant_code_layout_valid -- a gas variant keeps the code layout
 *)
Theory e2eDeployAtMarks
Ancestors
  e2eDeployDefs e2eDefs ctorDeployDefs deployUnitExecution deployUnitExitSafe
  ctorDeployMemoryFrontier ctorDeployImmBudget ctorDeployInitcode
  ctorDeployEntry ctorDeployShape ctorDeployDefsReach ctorDeployDead
  ctorDeployFrame compileVyper codegen e2eProducers e2eComposition e2eEntry
  o1PipelineCorrect o1PassContract codegenCorrectness passSimulationDefs
  lowerDloadDefs gasSummary vyperStorageFootprint
  memInvZeroPad removeUnusedGasProofs gasOracleReplay codegenEntryRel
  venomExecSemantics venomState

Theorem gas_readings_rel_mono:
  !readings P Q.
    gas_readings_rel readings P T /\ (!gs. P gs ==> Q gs) ==>
    gas_readings_rel readings Q T
Proof
  rw[gas_readings_rel_def] >> metis_tac[]
QED

Theorem deploy_exempt_result_rel[local]:
  deploy_source_exempt tops src ==>
  deploy_result_rel H tops runtime_bc tx es r es' src
Proof
  Cases_on `src` >> simp[deploy_source_exempt_def] >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[deploy_source_exempt_def, deploy_result_rel_def]
QED

Theorem gas_variant_code_layout_valid:
  gas_variant si so /\ code_layout_valid so ==> code_layout_valid si
Proof
  rw[gas_variant_def] >> qpat_x_assum `so = _` SUBST_ALL_TAC >>
  fs[code_layout_valid_def]
QED

(* The bridges at the deployment entry: the S4 memory facts of vs from its
   memory-safe and pointer-safe runs from "__deploy". *)
Theorem deploy_selected_memory:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  code_layout_valid vs /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__deploy" /\
  (!fuel. mem_safe_blocks fuel dunit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) /\
  (!fuel. ptr_safe_blocks D (imm_len tops) fuel dunit.cu_context func [] FEMPTY
     entry_taint
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                 vs_inst_idx := 0 |>)) ==>
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len tops) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs
Proof
  strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule deploy_imm_alloca_budget_ok >> strip_tac >>
  `imm_len tops + unit_alloca_budget dunit.cu_context < dimword (:256)` by
    decide_tac >>
  rpt conj_tac
  >- (qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `func`,
                   `"__deploy"`, `vs`] mp_tac lowered_unit_raw_memory_ok_from >>
      impl_tac >- fs[] >> simp[])
  >- (qspecl_then [`D`, `imm_len tops`, `dunit.cu_context`, `"__deploy"`,
                   `func`, `"__deploy"`, `vs`] mp_tac lowered_unit_ptr_taint >>
      impl_tac >- fs[] >> simp[])
  >- (qspecl_then [`D`, `imm_len tops`, `dunit.cu_context`, `"__deploy"`,
                   `func`, `"__deploy"`, `vs`] mp_tac lowered_unit_ptr_taint >>
      impl_tac >- fs[] >> simp[])
  >- (qspecl_then [`dunit.cu_context`, `"__deploy"`, `func`, `"__deploy"`,
                   `vs`] mp_tac lowered_unit_dload_offset_ok >>
      impl_tac >- fs[] >> simp[]) >>
  qspecl_then [`imm_len tops`, `dunit.cu_context`, `"__deploy"`, `func`, `vs`]
    mp_tac lowered_unit_dload_headroom_ok_from >>
  impl_tac >- fs[] >> simp[]
QED

(* The entry state's own facts: its callee outcomes, its code layout, and the
   compiled entry state's initial context relation. *)
Theorem deploy_entry_facts:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_outcomes = MAP SND (call_trace es) /\ code_layout_valid vs /\
  unit_shape_ok dout.po_unit /\
  initial_ctx_rel cplan prog dout.po_unit.cu_context
    (deploy_entry_state prog cplan tops es) (shadow_root es) /\
  o1_run_state_ok (deploy_entry_state prog cplan tops es)
Proof
  strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all deploy_initcode_half_bounded >> strip_tac >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout` by
    fs[deploy_phases_def] >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_entry_state_ok >> strip_tac >> simp[] >>
  conj_tac
  >- (qpat_assum `gas_variant _ _` mp_tac >>
      pure_rewrite_tac[gas_variant_def] >>
      disch_then (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_outcomes`) >>
      simp[deploy_entry_state_def, entry_venom_state_def]) >>
  irule gas_variant_code_layout_valid >>
  qexists_tac `deploy_entry_state prog cplan tops es` >>
  fs[o1_run_state_ok_def]
QED

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

(* The exit witness supplies the full target mask-entry bundle. *)
Theorem deploy_unit_exit_mask_entry:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es
   vs func sites marks src obs result r es'.
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
                     vs_inst_idx := 0 |>)) /\
    run_call es = SOME (r, es') /\
    ~creation_resource_starved es r es' ==>
    o1_lowered_inv dout.po_unit.cu_context
      (deploy_entry_state prog cplan tops es) /\
    ?fuel func_out lbl.
      dout.po_unit.cu_context.ctx_entry = SOME "__deploy" /\
      lookup_function "__deploy" dout.po_unit.cu_context.ctx_functions = SOME func_out /\
      fn_entry_label func_out = SOME lbl /\
      terminates (run_context fuel dout.po_unit.cu_context
        (deploy_entry_state prog cplan tops es)) /\
      gas_count_blocks fuel dout.po_unit.cu_context func_out
        ((deploy_entry_state prog cplan tops es) with
          <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) <=
        LENGTH (deploy_entry_state prog cplan tops es).vs_gas_readings
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_unit_exit_pipeline >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `exit_fuel` assume_tac)) >>
  drule_all deploy_entry_facts >> strip_tac >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  `o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all ctorDeployDefsReachTheory.deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all o1_pipeline_entry >> strip_tac >>
  qabbrev_tac `vo = deploy_entry_state prog cplan tops es` >>
  `?func_out. lookup_function "__deploy" dout.po_unit.cu_context.ctx_functions = SOME func_out` by
    (Cases_on `lookup_function "__deploy" dout.po_unit.cu_context.ctx_functions` >>
     fs[run_context_def, terminates_def]) >>
  rename1 `lookup_function "__deploy" dout.po_unit.cu_context.ctx_functions = SOME func_out` >>
  `?out_label. fn_entry_label func_out = SOME out_label` by
    (Cases_on `fn_entry_label func_out` >>
     fs[run_context_def, run_function_def, terminates_def]) >>
  rename1 `fn_entry_label func_out = SOME out_label` >>
  `vo.vs_initial_fmp = n2w cplan.cp_initial_fmp` by
    simp[Abbr `vo`, deploy_entry_state_def, entry_venom_state_def] >>
  `vo.vs_gas_readings = gas_readings (shadow_root es)` by
    fs[initial_ctx_rel_def, initial_ctx_rel_tail_def] >>
  `!k. ?Inv. codegen_context_obligations Inv dout.po_unit.cu_context cplan /\
      codegen_reachability_package Inv dout.po_unit.cu_context
        (vo with vs_gas_readings := gas_readings (shadow_root es) ++ REPLICATE k 0w)` by
    (gen_tac >>
     `o1_lowered_inv dout.po_unit.cu_context
        (vo with vs_gas_readings := gas_readings (shadow_root es) ++ REPLICATE k 0w)` by
       metis_tac[o1_lowered_inv_zero_pad] >>
     mp_tac (Q.SPECL [`dout`, `cplan`,
       `vo with vs_gas_readings := gas_readings (shadow_root es) ++ REPLICATE k 0w`]
       o1_pipeline_memory_obligations) >>
     impl_tac >- simp[] >>
     disch_then (qx_choose_then `pad_inv` strip_assume_tac) >>
     drule_all o1_pipeline_codegen_obligations >>
     strip_tac >> qexists_tac `pad_inv` >> simp[]) >>
  `vo with vs_gas_readings := gas_readings (shadow_root es) = vo` by
    simp[venom_state_component_equality] >>
  qpat_assum `!k. ?Inv. _`
    (qspec_then `0` (qx_choose_then `entry_inv` strip_assume_tac)) >> fs[] >>
  qpat_assum `vo with vs_gas_readings := gas_readings (shadow_root es) = vo`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qspecl_then [`exit_fuel`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `entry_inv`,
               `vo`, `shadow_root es`] mp_tac codegen_correct >>
  impl_tac >- fs[] >>
  disch_then (qx_choosel_then [`sr`, `sg`] strip_assume_tac) >>
  `?ctxt rb. es.contexts = [(ctxt, rb)]` by fs[deploy_state_rel_def] >>
  rename1 `es.contexts = [(root_ctxt, root_rb)]` >>
  drule_all deploy_shadow_not_starved >> strip_tac >> fs[] >>
  `?vf. run_context exit_fuel dout.po_unit.cu_context vo = Halt vf \/
        ?a. run_context exit_fuel dout.po_unit.cu_context vo = Abort a vf` by
    (Cases_on `run_context exit_fuel dout.po_unit.cu_context vo` >>
     gvs[venom_frame_rel_def, terminates_def] >> metis_tac[]) >>
  qabbrev_tac `gas_total = gas_count_blocks exit_fuel dout.po_unit.cu_context func_out
    (vo with <|vs_prev_bb := NONE; vs_current_bb := out_label; vs_inst_idx := 0|>)` >>
  `gas_replay_at gas_total (run_context exit_fuel dout.po_unit.cu_context) vo` by
    (`run_context exit_fuel dout.po_unit.cu_context =
      (\u. run_blocks exit_fuel dout.po_unit.cu_context func_out
        (u with <|vs_prev_bb := NONE; vs_current_bb := out_label; vs_inst_idx := 0|>))` by
       simp[FUN_EQ_THM, run_context_def, run_function_def] >>
     pop_assum SUBST1_TAC >>
     irule (BETA_RULE (Q.INST [`h` |-> `\u. u with <|vs_prev_bb := NONE;
                    vs_current_bb := out_label; vs_inst_idx := 0|>`,
                   `f` |-> `run_blocks exit_fuel dout.po_unit.cu_context func_out`]
        remove_unused_replay_count_preupdate)) >>
     simp[venom_state_component_equality] >>
     qunabbrev_tac `gas_total` >>
     irule remove_unused_blocks_successful_replay_count >>
     Cases_on `run_blocks exit_fuel dout.po_unit.cu_context func_out
       (vo with <|vs_prev_bb := NONE; vs_current_bb := out_label; vs_inst_idx := 0|>)` >>
     gvs[run_context_def, run_function_def, terminates_def]) >>
  `gas_total <= LENGTH (gas_readings (shadow_root es))` by
    (irule (Q.SPECL [`exit_fuel`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`,
      `vo`, `shadow_root es`, `sr`, `sg`, `gas_total`]
      codegen_gas_replay_count_bound) >> simp[] >> metis_tac[]) >>
  qexists_tac `exit_fuel` >> fs[Abbr `gas_total`]
QED

(* At one tail of gas readings past the marked ones, where the constructor
   run's storage guard holds. *)
Theorem deploy_correct_at_tail[local]:
  compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  ~(?t. runtime_bc = 0xEFw :: t) /\
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
  deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vs /\
  run_call es = SOME (r, es') /\
  deploy_storage_ok tops am tx vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
  creation_resource_starved es r es' \/
  deploy_result_rel
    (storage_trace_horizon
       (deploy_storage_trace (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am tx tops))
    tops runtime_bc tx es r es'
    (load_contract (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE, tops)] [])
Proof
  strip_tac >>
  drule compile_vyper_runtime_nonempty >> strip_tac >>
  drule_all deploy_entry_facts >> strip_tac >>
  Cases_on `deploy_source_exempt tops
              (load_contract (SOME vs.vs_outcomes)
                 (gas_explicit marks vs.vs_gas_readings ++ tail) am tx
                 [(NONE, tops)] [])`
  >- (disj2_tac >> irule deploy_exempt_result_rel >> first_assum ACCEPT_TAC) >>
  drule_all deploy_unit_run_entry >> strip_tac >>
  drule_all deploy_unit_shape_ok >> strip_tac >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  qspecl_then [`marks`, `tops`, `runtime_bc`, `am`, `tx`, `dunit`, `vs`, `tail`]
    mp_tac deploy_unit_exit_safe_runs >>
  impl_tac >- fs[] >> strip_tac >>
  qabbrev_tac `H = storage_trace_horizon
    (deploy_storage_trace (SOME vs.vs_outcomes)
       (gas_explicit marks vs.vs_gas_readings ++ tail) am tx tops)` >>
  drule_all deploy_selected_memory >> strip_tac >>
  `ctx_sim (deploy_dead H tops runtime_bc am tx) dunit.cu_context
     dout.po_unit.cu_context vs (deploy_entry_state prog cplan tops es) /\
   o1_lowered_inv dout.po_unit.cu_context
     (deploy_entry_state prog cplan tops es)` by
    (qpat_assum `!D. dead_wf D ==> _`
       (qspec_then `deploy_dead H tops runtime_bc am tx` mp_tac) >>
     impl_tac >- fs[deploy_dead_wf] >> impl_tac >- fs[] >> simp[]) >>
  `terminates (run_context fuel dunit.cu_context vs)` by
    metis_tac[deploy_venom_result_rel_terminates] >>
  `?fuel'. dead_result_rel (deploy_dead H tops runtime_bc am tx)
             (run_context fuel dunit.cu_context vs)
             (run_context fuel' dout.po_unit.cu_context
                (deploy_entry_state prog cplan tops es))` by
    metis_tac[ctx_sim_def] >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `am`, `tx`, `SOME vs.vs_outcomes`,
               `gas_explicit marks vs.vs_gas_readings ++ tail`,
               `load_contract (SOME vs.vs_outcomes)
                  (gas_explicit marks vs.vs_gas_readings ++ tail) am tx
                  [(NONE, tops)] []`,
               `run_context fuel dunit.cu_context vs`,
               `run_context fuel' dout.po_unit.cu_context
                  (deploy_entry_state prog cplan tops es)`] mp_tac
    deploy_venom_result_rel_dead >>
  impl_tac >- fs[] >> strip_tac >>
  `(deploy_entry_state prog cplan tops es).vs_initial_fmp =
     n2w cplan.cp_initial_fmp` by
    simp[deploy_entry_state_def, entry_venom_state_def] >>
  `o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all o1_pipeline_memory_obligations >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  qspecl_then [`fuel'`, `rpolicy`, `dout.po_unit`, `cplan`, `prog`, `Inv`,
               `deploy_entry_state prog cplan tops es`, `shadow_root es`] mp_tac
    codegen_correct >>
  impl_tac >- fs[] >> disch_tac >>
  qspecl_then [`H`, `tops`, `runtime_bc`, `deploy_bc`, `am`, `tx`, `es`,
               `load_contract (SOME vs.vs_outcomes)
                  (gas_explicit marks vs.vs_gas_readings ++ tail) am tx
                  [(NONE, tops)] []`,
               `run_context fuel' dout.po_unit.cu_context
                  (deploy_entry_state prog cplan tops es)`] mp_tac
    deploy_venom_frame >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> gvs[]
QED

(* TOP-LEVEL.  Where the frame is not starved, every filling of its gas
   readings that meets the constructor run's storage guard extends the marked
   readings of some raw entry state vs carrying the S4 facts and the
   selected-run certificate at its marks; then the deploy result relation
   holds at every filling. *)
Theorem e2e_deploy_correct_from_gas_link:
  !policy tops deploy_bc runtime_bc am tx es r es' rpolicy dunit dout prog cplan.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    ~(?t. runtime_bc = 0xEFw :: t) /\
    run_call es = SOME (r, es') /\
    (creation_resource_starved es r es' \/
     gas_readings_rel (gas_readings es)
       (\gs. deploy_storage_ok tops am tx (MAP SND (call_trace es)) gs ==>
             ?vs marks tail.
               gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
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
               deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vs) T)
    ==>
    creation_resource_starved es r es' \/
    deploy_call_result_rel tops runtime_bc am tx es r es'
Proof
  rpt strip_tac >>
  Cases_on `creation_resource_starved es r es'` >> fs[] >>
  simp[deploy_call_result_rel_def] >>
  drule gas_readings_rel_mono >> disch_then irule >>
  rpt gen_tac >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `deploy_storage_ok _ _ _ _ gs ==> _` drule >> strip_tac >>
  gvs[] >>
  drule_all deploy_entry_facts >> strip_tac >>
  qpat_x_assum `vs.vs_outcomes = _` (SUBST_ALL_TAC o SYM) >>
  `~(?t. runtime_bc = 0xEFw :: t)` by fs[] >>
  drule_all deploy_correct_at_tail >> strip_tac >> fs[]
QED
