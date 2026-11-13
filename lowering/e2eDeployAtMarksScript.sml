(*
 * e2e_deploy_correct_at_marks: the deploy theorem at one fixed gas marking,
 * the deployment twin of e2eCallAtMarks.
 *
 * The caller supplies the raw deployment unit's entry state vs (a gas
 * variant of the compiled run's entry state), the S4 simulation facts on it
 * for every well-formed dead mask, the selected-run certificate at marks,
 * and that every filling of the frame's gas readings extends the marked
 * readings of vs.  At each such filling, the exit arm gives the entry's
 * memory- and pointer-safe runs at the run's own storage horizon H
 * (deployUnitExitSafe); the ctorDeployMemoryFrontier bridges turn them into
 * the S4 memory facts, which give ctx_sim at deploy_dead H; codegen and the
 * creation frame finish.
 *
 * TOP-LEVEL:
 *   e2e_deploy_correct_at_marks -- the deploy result relation at every
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
Theorem deploy_selected_memory[local]:
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
Theorem deploy_entry_facts[local]:
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
  frame_resource_starved es r es' \/
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
  >- (disj2_tac >> drule deploy_exempt_result_rel >> simp[]) >>
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
               `gas_explicit marks vs.vs_gas_readings ++ tail`] mp_tac
    deploy_venom_result_rel_dead >>
  simp[] >> disch_then drule_all >> strip_tac >>
  `(deploy_entry_state prog cplan tops es).vs_initial_fmp =
     n2w cplan.cp_initial_fmp` by
    simp[deploy_entry_state_def, entry_venom_state_def] >>
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

(* TOP-LEVEL.  The last premise links the frame's gas readings to the marked
   readings of vs: every filling the readings allow extends them. *)
Theorem e2e_deploy_correct_at_marks:
  !policy tops deploy_bc runtime_bc am tx es rpolicy dunit dout prog cplan vs
   marks.
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
    gas_readings_rel (gas_readings es)
      (\gs. ?tail. gs = gas_explicit marks vs.vs_gas_readings ++ tail) T
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `frame_resource_starved es r es'` >> simp[] >>
  drule_all deploy_entry_facts >> strip_tac >>
  qpat_x_assum `vs.vs_outcomes = _` (SUBST_ALL_TAC o SYM) >>
  simp[deploy_call_result_rel_def] >>
  irule gas_readings_rel_mono >>
  qexists_tac `\gs. ?tail. gs = gas_explicit marks vs.vs_gas_readings ++ tail` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  drule_all deploy_correct_at_tail >> strip_tac >> fs[]
QED
