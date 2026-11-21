(* Deploy-phase correctness (PLAN §5.11): e2e_deploy_correctness, the
 * constructor's run in a creation frame installs the runtime code and the
 * immutables section.  Kept apart from e2eCorrectness so the deploy work
 * owns its own file. *)
Theory e2eDeployCorrectness
Ancestors
  ownSymSrcUnit codegenLabelDisciplined fnPlanPlaceRevertPostamble
  codegenSymOwnRel
  e2eDeployAtMarks e2eDeployRawFmp e2eDeployDefs ctorDeployDefs
  ctorDeployInitcode ctorDeployEntry ctorDeployShape ctorDeployDefsReach
  deployUnitExecution ctorDeployBodyJoint ctorDeployDead ctorDeployFrame
  compileVyper compilePhasesProps codegen e2eProducers e2eComposition
  o1PipelineCorrect o1PassContract codegenCorrectness passSimulationDefs
  lowerDloadDefs e2eEntry gasSummary asmOptimizer
  deployUnitExitSafe ctorDeployMemoryFrontier o1SafeUpto unitMemInv
  o1PipelineCompose deployUnitProducers ctorDeployRawEntryFacts
  asmOptNonemptyFinalizer asmOptNonemptyWitness asmFrameRel deployFrameReplay
  callTrace unitTransformDefs gasMaskProjection gasEvents gasExplicitSites codegenSymRel
  deploySymSrcUnit e2eDefs list venomState gasFocusPrefixDriver

(* A successful compilation exposes the deployment unit's phases. *)
Theorem compile_vyper_deploy_phases:
  compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) ==>
  ?rpolicy dunit dout prog cplan.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan)
Proof
  simp[compile_vyper_def, deploy_phases_def] >> strip_tac >>
  drule compile_vyper_with_success_phases >> strip_tac >>
  gvs[finalize_codegen_identity, o1PipelineCorrectTheory.o1_pipeline_def,
      AllCaseEqs()] >>
  qpat_x_assum `codegen_assembly rpolicy deploy_out.po_unit = SOME _`
    (strip_assume_tac o MATCH_MP codegen_assembly_success_shape) >>
  goal_assum $ drule_at Any >> gvs[]
QED

(* On the selected nonexempt filling the exit certificate covers the whole
   raw run. The caller's dead mask supplies the pre-walk invariant. *)
Theorem deploy_selected_producer_inputs[local]:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  deploy_unit_execution_correct_at marks tops runtime_bc am tx dunit vs /\
  deploy_storage_ok tops am tx vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ tail) /\
  ~deploy_source_exempt tops
    (load_contract (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx [(NONE, tops)] []) /\
  raw_unit_memory_ok dunit.cu_context vs /\
  ptr_discipline (imm_len tops) dunit.cu_context vs /\
  taint_within D dunit.cu_context vs /\
  mem_inv dload_offset_ok dunit.cu_context vs /\
  mem_inv dload_headroom_ok dunit.cu_context vs ==>
  (?fuel. terminates (run_context fuel dunit.cu_context vs)) /\
  o1_pre_walk_inv D dunit.cu_context vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                            s.vs_code = vs.vs_code /\
                            s.vs_data_section = vs.vs_data_section)
    dunit.cu_context vs
Proof
  strip_tac >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit` by
    fs[deploy_phases_def] >>
  drule lower_vyper_deploy_unit_context_ok >> strip_tac >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  drule_all deploy_unit_exit_safe_runs >> strip_tac >>
  conj_tac >- metis_tac[deploy_venom_result_rel_terminates] >>
  conj_tac
  >- (`mem_inv raw_mem_ok dunit.cu_context vs` by
        (qpat_x_assum `raw_unit_memory_ok _ _` mp_tac >>
         simp[unitTransformDefsTheory.raw_unit_memory_ok_def, mem_inv_def,
              raw_mem_ok_def]) >>
      irule o1_source_pre_walk_inv >>
      simp[o1_src_inv_def] >> metis_tac[source_fmp_free]) >>
  `!fn inst s. raw_reachable vs dunit.cu_context fn inst s ==>
     inst_dload_in_section inst s` by
    (rpt strip_tac >> irule lowered_unit_dload_in_section >> metis_tac[]) >>
  simp[mem_inv_raw_reachable] >> metis_tac[raw_reachable_code_data]
QED

(* Start the backend producer at the constructor's execution-only frame,
   retaining the observations of the real creation frame. *)
Theorem deploy_focus_frame_inputs[local]:
  deploy_phases policy tops (assemble prog, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_state_rel tops (assemble prog') am tx es /\
  vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
  deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
  fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
  unit_shape_ok dout.po_unit /\
  run_call es = SOME (r, es') /\ ~creation_resource_starved es r es' ==>
  o1_run_state_ok vs_out /\
  vs_out.vs_code = assemble prog' ++ vs_out.vs_data_section /\
  LENGTH vs_out.vs_data_section < dimword (:256) DIV 2 /\
  vs_out.vs_outcomes = MAP SND (call_trace es) /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cplan prog vs_out
    (entry_asm_state vs_out (shadow_root es)) /\
  asm_frame_rel_tail [] prog' vs_out.vs_data_section (shadow_root es)
    (entry_asm_state vs_out (shadow_root es)) (shadow_root es) /\
  gas_readings (shadow_root es) = gas_readings es /\
  ?sr sg. run_call (shadow_root es) = SOME (sr,sg) /\
          ~frame_resource_starved (shadow_root es) sr sg
Proof
  strip_tac >>
  `codegen_assembly rpolicy dout.po_unit = SOME prog` by fs[deploy_phases_def] >>
  `assemble prog <> []` by
    metis_tac[codegen_assembly_terminal_witness, terminal_witness_assemble_nonempty] >>
  `assemble prog' <> []` by
    (Cases_on `fin = K SOME` >- gvs[] >>
     `fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
     metis_tac[codegen_assembly_finalizer_nonempty]) >>
  `?ctxt rb. es.contexts = [(ctxt,rb)] /\ ~ctxt.msgParams.static` by
    fs[deploy_state_rel_def] >>
  drule_all deploy_shadow_run_not_starved >> strip_tac >>
  `frame_obs (shadow_root es) = frame_obs es` by
    (irule shadow_root_frame_obs >> simp[]) >>
  `vs_out.vs_fmp = vs_out.vs_initial_fmp /\
   o1_initial_state_ok vs_out /\ ~vs_out.vs_call_ctx.cc_static /\
   vs_out.vs_outcomes = MAP SND (call_trace es)` by
    simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def,
         entry_venom_state_def, venomStateTheory.init_venom_state_def,
         o1_initial_state_ok_def] >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`]
    mp_tac opt_deploy_asm_rels_own >>
  impl_tac >- simp[] >> strip_tac >>
  `tx with code := vs_out.vs_code = tx` by
    metis_tac[deploy_own_txp_identity] >>
  `deploy_source_ok tops am tx` by fs[] >>
  `code_layout_valid vs_out` by
    (Q.SUBGOAL_THEN
      `code_layout_valid
          (vs_out with <|vs_gas_readings := []; vs_fmp := 0w;
                         vs_initial_fmp := 0w|>)` mp_tac
     >- (qpat_assum `vs_out = _` (fn th => rewrite_tac[th]) >>
         irule deploy_raw_entry_code_layout >> metis_tac[]) >>
     simp[code_layout_valid_def]) >>
  `vs_out.vs_code = assemble prog' ++ vs_out.vs_data_section` by fs[] >>
  `LENGTH vs_out.vs_data_section < dimword (:256) DIV 2` by
    (`0 < LENGTH (assemble prog')` by (Cases_on `assemble prog'` >> fs[]) >>
     qpat_assum `code_layout_valid vs_out`
       (strip_assume_tac o REWRITE_RULE [code_layout_valid_def]) >>
     qpat_assum `LENGTH vs_out.vs_code <= _` mp_tac >>
     qpat_assum `vs_out.vs_code = assemble prog' ++ _`
       (fn th => REWRITE_TAC [th, listTheory.LENGTH_APPEND]) >>
     qpat_assum `0 < LENGTH (assemble prog')` mp_tac >> decide_tac) >>
  fs[o1_run_state_ok_def, asm_frame_rel_tail_nil, gas_readings_def]
QED

Theorem deploy_gas_link_from_focus[local]:
  (!rpolicy unit out vs0 cpl prog fin prog' es0 nm entryfn lbl fmp markf
    lo (project : (string # num) -> bool) result final.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_run_state_ok vs0 /\ unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_own_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
    codegen_asm_entry_rel_reloc (lo_reloc prog prog') cpl prog vs0
      (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final ==>
    ?raw_slots sites unused.
      LENGTH raw_slots = LENGTH sites /\
      PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
      !raw.
        LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
        (?rest. MAP project sites = markf (raw ++ [0w]) ++ rest) /\
        !D.
          (?fr. terminates (run_context fr unit.cu_context
             (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
          dead_wf D /\
          o1_pre_walk_inv D unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
          (fin = asm_opt_finalizer ==>
             mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                       s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
               unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
          ctx_sim D unit.cu_context out.po_unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
          ctx_abort_rq D unit.cu_context out.po_unit.cu_context
            (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
          (fin = asm_opt_finalizer ==>
             code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context) /\
          o1_lowered_inv out.po_unit.cu_context vs0) ==>
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs_out fmp r es'.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    (?shadow_ctx. !vs.
       raw_variant fmp vs vs_out ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs) /\
    run_call es = SOME (r, es') /\
    ~creation_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. deploy_storage_ok tops am (tx with code := vs_out.vs_code) (MAP SND (call_trace es)) gs ==>
            ?vs marks tail.
              gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
              raw_variant fmp vs vs_out /\
              (~deploy_source_exempt tops
                 (load_contract (SOME vs.vs_outcomes)
                   (gas_explicit marks vs.vs_gas_readings ++ tail)
                   am (tx with code := vs_out.vs_code) [(NONE, tops)] []) ==>
               !D. dead_wf D ==>
                 raw_unit_memory_ok dunit.cu_context vs /\
                 ptr_discipline (imm_len tops) dunit.cu_context vs /\
                 taint_within D dunit.cu_context vs /\
                 mem_inv dload_offset_ok dunit.cu_context vs /\
                 mem_inv dload_headroom_ok dunit.cu_context vs ==>
                 ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
                   vs_out /\
                 (fin = asm_opt_finalizer ==>
                    code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context) /\
                 o1_lowered_inv dout.po_unit.cu_context
                   vs_out) /\
              deploy_unit_execution_correct_at marks tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
   o1PipelineCorrect$o1_pipeline rpolicy dunit = SOME dout /\
   codegen_assembly rpolicy dout.po_unit = SOME prog /\
   generate_context_plan dout.po_unit.cu_context = SOME cplan` by
    fs[deploy_phases_def] >>
  drule_all deploy_unit_o1_shape_ok >> strip_tac >>
  drule_all deploy_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  drule_all deploy_focus_frame_inputs >> strip_tac >>
  rename1 `run_call (shadow_root es) = SOME (sr,sg)` >>
  drule lower_vyper_deploy_unit_entry >> strip_tac >>
  rename1 `lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func` >>
  drule_all deploy_raw_fmp_focus_mask_entry >>
  disch_then (qx_choose_then `markf` assume_tac) >>
  `fn_entry_label func = SOME "__deploy"` by
    (qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (mp_tac o REWRITE_RULE [deploy_unit_execution_correct_with_def] o
        CONJUNCT1 o Q.SPEC `[]`) >>
     disch_then (qx_choosel_then [`df`, `shadow_df`] strip_assume_tac) >>
     `df = func` by fs[] >> fs[]) >>
  `fin = asm_opt_finalizer ==>
     label_flow_own_ok dunit.cu_context /\
     (!fn inst. MEM fn dunit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                       ds.ds_items) dunit.cu_data_segment /\
     ((?fn inst. MEM fn dunit.cu_context.ctx_functions /\
                 MEM inst (fn_insts fn) /\
                 MEM (Label "runtime_begin") inst.inst_operands) ==>
      EXISTS (\ds. ds.ds_label = "runtime_begin") dunit.cu_data_segment) /\
     LENGTH vs_out.vs_data_section < dimword (:256) DIV 2` by
    (disch_tac >>
     qspecl_then [`policy`, `tops`, `assemble prog`, `runtime_bc`,
                   `rpolicy`, `dunit`, `dout`, `prog`, `cplan`] mp_tac
       lower_vyper_deploy_unit_sym_src_ok_own >>
     impl_tac >- fs[deploy_source_ok_def] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `unit_alloca_budget dunit.cu_context +
     32 * ctx_dload_count dunit.cu_context <= w2n fmp` by decide_tac >>
  qpat_x_assum `!rpolicy unit out vs0 cpl prog fin prog' es0 nm entryfn lbl fmp markf
                   lo project result final. _` mp_tac >>
  disch_then (mp_tac o Q.SPECL [
    `rpolicy`, `dunit`, `dout`, `vs_out`, `cplan`, `prog`, `fin`, `prog'`,
    `shadow_root es`, `"__deploy"`, `func`, `"__deploy"`, `fmp`, `markf`,
    `imm_len tops`, `\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx`,
    `sr`, `sg` ]) >>
  impl_tac
  >- (BETA_TAC >> asm_rewrite_tac[] >> gen_tac >>
      qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
        (mp_tac o CONJUNCT2 o Q.SPEC `gs`) >>
      simp[]) >>
  disch_then (qx_choosel_then [`raw_slots`, `sites`, `unused`] strip_assume_tac) >>
  qabbrev_tac `project = MAP
    (\key. key IN gas_explicit_sites dunit.cu_context shadow_ctx) sites` >>
  rewrite_tac[gas_readings_rel_def] >>
  irule gas_mask_projection >>
  qexistsl_tac [`project`, `raw_slots`, `unused`] >>
  `LENGTH project = LENGTH raw_slots` by simp[Abbr `project`] >>
  `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es)` by
    (qpat_assum `gas_readings (shadow_root es) = gas_readings es`
       (fn th => once_rewrite_tac [GSYM th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `LENGTH project = LENGTH raw_slots` (fn lengths =>
    qpat_assum `PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es)`
      (fn readings => rewrite_tac [lengths, readings])) >>
  qx_genl_tac [`raw`, `tail`] >> strip_tac >> BETA_TAC >>
  qpat_x_assum `!raw. LIST_REL _ raw_slots raw ==> _` (qspec_then `raw` mp_tac) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `rest` assume_tac) assume_tac) >>
  qabbrev_tac `vs = vs_out with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp;
                                    vs_initial_fmp := fmp|>` >>
  qabbrev_tac `marks = markf (raw ++ [0w])` >>
  qabbrev_tac `suffix = gas_explicit rest (DROP (LENGTH marks) (raw ++ [0w])) ++ tail` >>
  `gas_explicit project raw ++ tail = gas_explicit marks vs.vs_gas_readings ++ suffix` by
    (qpat_assum `project = marks ++ rest` (fn th => once_rewrite_tac [th]) >>
     simp[Abbr `suffix`, Abbr `vs`] >>
     irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`tail` |-> `[]:bytes32 list`] gas_mask_padded_split)) >>
     `LENGTH raw_slots = LENGTH raw` by metis_tac[LIST_REL_LENGTH] >> fs[]) >>
  `raw_variant fmp vs vs_out /\ vs.vs_outcomes = MAP SND (call_trace es)` by
    simp[Abbr `vs`, raw_variant_def, gas_variant_def, venom_state_component_equality] >>
  `deploy_unit_execution_correct_at marks tops runtime_bc am
     (tx with code := vs_out.vs_code) dunit vs` by
    (rewrite_tac[deploy_unit_execution_correct_at_with] >>
     qexists_tac `shadow_ctx` >>
     qunabbrev_tac `marks` >> qunabbrev_tac `vs` >>
     qpat_assum `!gs. deploy_unit_execution_correct_with _ _ _ _ _ _ _ _ /\ _`
       (ACCEPT_TAC o CONJUNCT1 o Q.SPEC `raw ++ [0w]`)) >>
  disch_tac >> qexistsl_tac [`vs`, `marks`, `suffix`] >>
  qpat_assum `raw_variant fmp vs vs_out` (fn raw_variant_thm =>
    qpat_assum `deploy_unit_execution_correct_at marks _ _ _ _ dunit vs` (fn cert =>
      qpat_assum `gas_explicit project raw ++ tail = _`
        (fn readings => rewrite_tac [raw_variant_thm, cert, readings]))) >>
  disch_tac >> qx_gen_tac `D` >> disch_tac >>
  disch_then strip_assume_tac >>
  `deploy_storage_ok tops am (tx with code := vs_out.vs_code) vs.vs_outcomes
       (gas_explicit marks vs.vs_gas_readings ++ suffix)` by
    (qpat_assum `gas_explicit project raw ++ tail = _`
       (fn th => once_rewrite_tac [GSYM th]) >>
     qpat_assum `vs.vs_outcomes = _` (fn th => rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  drule_all deploy_selected_producer_inputs >> strip_tac >>
  qpat_x_assum `!D. (?fr. terminates _) /\ _ ==> _` (qspec_then `D` mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rename1 `terminates (run_context fuel dunit.cu_context vs)` >>
          qexists_tac `fuel` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      disch_tac >>
      `vs.vs_code = vs_out.vs_code /\ vs.vs_data_section = vs_out.vs_data_section` by
        simp[Abbr `vs`] >>
      qpat_assum `vs.vs_code = _` (fn code =>
        qpat_assum `vs.vs_data_section = _` (fn data =>
          qpat_assum `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\ _) _ vs`
            (ACCEPT_TAC o REWRITE_RULE [code, data])))) >>
  strip_tac >> asm_rewrite_tac[]
QED

(* The raw_slots mask and the sites-to-slots link.
   Where the frame is not starved, every filling of its gas readings that
   meets the constructor run's storage guard extends the marked readings of
   a raw entry state carrying the S4 facts and the selected-run certificate.
   Proved from the gas focus producer. *)
Theorem deploy_pipeline_gas_link:
  !fin policy tops runtime_bc rpolicy dunit dout prog prog' cplan am tx es vs_out fmp r es'.
    fin IN accepted_finalizers /\
    fin rpolicy prog = SOME prog' /\
    deploy_phases policy tops (assemble prog, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_state_rel tops (assemble prog') am tx es /\
    LENGTH (call_trace es) < 2 ** 64 /\
    vs_out = opt_deploy_entry_state_own prog prog' cplan tops es /\
    deploy_source_ok tops am (tx with code := vs_out.vs_code) /\
    w2n vs_out.vs_initial_fmp <= w2n fmp /\
    w2n fmp < 2 ** 254 /\
    imm_len tops + unit_alloca_budget dunit.cu_context +
      32 * ctx_dload_count dunit.cu_context <= w2n fmp /\
    (?shadow_ctx. !vs.
       raw_variant fmp vs vs_out ==>
       ?marks. deploy_unit_execution_correct_with shadow_ctx marks
         tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs) /\
    run_call es = SOME (r, es') /\
    ~creation_resource_starved es r es' ==>
    gas_readings_rel (gas_readings es)
      (\gs. deploy_storage_ok tops am (tx with code := vs_out.vs_code) (MAP SND (call_trace es)) gs ==>
            ?vs marks tail.
              gs = gas_explicit marks vs.vs_gas_readings ++ tail /\
              raw_variant fmp vs vs_out /\
              (~deploy_source_exempt tops
                 (load_contract (SOME vs.vs_outcomes)
                   (gas_explicit marks vs.vs_gas_readings ++ tail)
                   am (tx with code := vs_out.vs_code) [(NONE, tops)] []) ==>
               !D. dead_wf D ==>
                 raw_unit_memory_ok dunit.cu_context vs /\
                 ptr_discipline (imm_len tops) dunit.cu_context vs /\
                 taint_within D dunit.cu_context vs /\
                 mem_inv dload_offset_ok dunit.cu_context vs /\
                 mem_inv dload_headroom_ok dunit.cu_context vs ==>
                 ctx_sim D dunit.cu_context dout.po_unit.cu_context vs
                   vs_out /\
                 (fin = asm_opt_finalizer ==>
                    code_end_offset_ok (raw_reachable vs_out) dout.po_unit.cu_context) /\
                 o1_lowered_inv dout.po_unit.cu_context
                   vs_out) /\
              deploy_unit_execution_correct_at marks tops runtime_bc am (tx with code := vs_out.vs_code) dunit vs)
Proof
  mp_tac deploy_gas_link_from_focus >>
  impl_tac
  >- (rpt gen_tac >>
      disch_then (ACCEPT_TAC o MATCH_MP focus_producer_finalizer_own)) >>
  disch_then (fn th =>
    rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
    qspecl_then [`fin`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
      `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`,
      `vs_out`, `fmp`, `r`, `es'`] mp_tac th >>
    asm_rewrite_tac [])
QED

(* The -O none case of e2e_deploy_correctness: PLAN 5.11, D28, section 9.
 * Proved from the deployment pieces
 * (ctorDeploy* theories) and the generic O1 pipeline and codegen stages.
 * Not on the logical dependency path of call correctness.
 *
 * Proof idea: relate the constructor's CODECOPY-decoded canonical
 * ABI tail to source binding, simulate its body and runtime-return
 * epilogue, then apply Verifereum handle_create/handle_exception in the SINGLE
 * fresh creation frame. Deposit gas/size failures are resource starvation.
 * Exclude the 0xEF runtime prefix. Match installed runtime code and all remaining
 * account fields, transient storage and logs; use explicit source failure
 * cases, exempting only the existing exact dynamic ABI strictness predicate.
 *
 * The constructor's oracle uses the creation frame's call outcomes.
 * The source gas observations are related to the frame's GAS readings.
 * The entry relation supplies the arguments via constructor_args_encode.
 *
 * A constructor that halts (selfdestruct) makes load_contract succeed without
 * installing the source at tx.target, so that INL is told apart by
 * ALOOKUP am'.sources tx.target = NONE (deploy_state_rel has it NONE at
 * entry). Then the EVM frame halts with empty output and deposits no code, and
 * the accounts after the pending deletions, transient storage and logs agree
 * as in a halting call (call_result_rel_at).
 *)
Theorem e2e_deploy_correctness_identity:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  rpt strip_tac >>
  drule compile_vyper_deploy_phases >> strip_tac >>
  `K SOME IN accepted_finalizers` by simp[asmOptimizerTheory.accepted_finalizers_def] >>
  `K SOME <> asm_opt_finalizer` by
    (strip_tac >>
     qpat_x_assum `K SOME = asm_opt_finalizer`
       (fn th => mp_tac (Q.AP_THM
         (Q.AP_THM th `rpolicy with rpol_final_assembly := FAP_Optimize`)
         `[AsmOp "STOP"; AsmOp "STOP"]`)) >>
     EVAL_TAC) >>
  drule_all compile_vyper_runtime_not_ef >> strip_tac >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `creation_resource_starved es r es'` >> simp[] >>
  `~frame_resource_starved es r es'` by
    (fs[frameOutcomeTheory.creation_resource_starved_def,
        frameOutcomeTheory.frame_resource_starved_def] >> metis_tac[]) >>
  `deploy_bc = assemble prog` by fs[deploy_phases_def] >> gvs[] >>
  `K SOME rpolicy prog = SOME prog` by simp[] >>
  `tx with code := (opt_deploy_entry_state_own prog prog cplan tops es).vs_code = tx`
    by metis_tac[deploy_own_txp_identity] >>
  drule deploy_raw_fmp_exists >>
  disch_then (qspecl_then [`prog`, `es`] strip_assume_tac) >>
  drule_all deploy_unit_execution_correct_raw_fmp >>
  disch_then (qspec_then `fmp` strip_assume_tac) >>
  qspecl_then [`K SOME`, `policy`, `tops`, `runtime_bc`, `rpolicy`, `dunit`,
               `dout`, `prog`, `prog`, `cplan`, `am`, `tx`, `es`,
               `opt_deploy_entry_state_own prog prog cplan tops es`, `fmp`, `r`, `es'`]
    mp_tac deploy_pipeline_gas_link >>
  impl_tac >- (fs[] >> metis_tac[]) >> strip_tac >>
  qspecl_then [`K SOME`, `policy`, `tops`, `assemble prog`, `runtime_bc`,
               `rpolicy`, `dunit`, `dout`, `prog`, `prog`, `cplan`, `am`, `tx`,
               `tx`, `es`, `opt_deploy_entry_state_own prog prog cplan tops es`,
               `fmp`, `r`, `es'`] mp_tac e2e_deploy_correct_from_gas_link >>
  impl_tac >- gvs[] >> simp[]
QED

(* The assembly optimizer case uses the installed code and relocated labels. *)
Theorem e2e_deploy_correctness_asm_opt:
  !policy tops deploy_bc runtime_bc am tx es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_vyper_deploy_phases_asm_opt >> strip_tac >>
  `asm_opt_finalizer IN accepted_finalizers` by simp[accepted_finalizers_def] >>
  drule_all compile_vyper_runtime_not_ef >> strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `creation_resource_starved es r es'` >> simp[] >>
  `deploy_state_rel tops (assemble prog') am tx es` by fs[] >>
  `deploy_source_ok tops am tx` by simp[deploy_source_ok_def] >>
  drule deploy_raw_fmp_exists >>
  disch_then (qspecl_then [`prog'`, `es`] strip_assume_tac) >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
    `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `fmp`] mp_tac
    deploy_unit_execution_correct_raw_fmp >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qabbrev_tac `vs_out = opt_deploy_entry_state_own prog prog' cplan tops es` >>
  `tx with code := vs_out.vs_code = tx` by
    (simp[Abbr `vs_out`] >> metis_tac[deploy_own_txp_identity]) >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `runtime_bc`, `rpolicy`,
    `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`, `es`, `vs_out`, `fmp`,
    `r`, `es'`] mp_tac deploy_pipeline_gas_link >>
  impl_tac >- (asm_simp_tac bool_ss [Abbr `vs_out`] >>
                qexists_tac `shadow_ctx` >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qspecl_then [`asm_opt_finalizer`, `policy`, `tops`, `deploy_bc`, `runtime_bc`,
    `rpolicy`, `dunit`, `dout`, `prog`, `prog'`, `cplan`, `am`, `tx`,
    `tx with code := vs_out.vs_code`, `es`, `vs_out`, `fmp`, `r`, `es'`] mp_tac
    e2e_deploy_correct_from_gas_link >>
  impl_tac >- (asm_simp_tac bool_ss [Abbr `vs_out`] >>
                qpat_assum `~(?t. runtime_bc = _::t)` mp_tac >> simp[]) >>
  asm_simp_tac bool_ss []
QED

(* TOP-LEVEL: one theorem over the accepted finalizers (Python's -O none and
   O1 final assembly). *)
Theorem e2e_deploy_correctness:
  !fin policy tops deploy_bc runtime_bc am tx es.
    fin IN accepted_finalizers /\
    compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ supported_program_deploy tops /\
    deploy_typing_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    LENGTH (call_trace es) < 2 ** 64
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (creation_resource_starved es r es' \/
       deploy_call_result_rel tops runtime_bc am tx es r es')
Proof
  rpt gen_tac >> strip_tac >>
  `fin = K SOME \/ fin = asm_opt_finalizer` by fs[accepted_finalizers_def] >>
  pop_assum strip_assume_tac >> pop_assum SUBST_ALL_TAC
  >- (drule_all e2e_deploy_correctness_identity >> simp[])
  >> drule_all e2e_deploy_correctness_asm_opt >> simp[]
QED

(* Typed kernel schema gate. This is an ML check, not a proved alias, and adds
 * no theorem dependency. The clean result-case definition must expand to
 * precisely the literal 5.11 conclusion above, including its explicit failure
 * cases and no-prefix guard. Whether the theorem depends on a cheat is
 * checked with `holbuild check`.
 *)
val savedDeploymentAdmission = DB.fetch "e2eDeployCorrectness" "e2e_deploy_correctness";
val _ =
  let
    val expected = ``!fin policy tops deploy_bc runtime_bc am tx es.
      fin IN accepted_finalizers /\
      compile_vyper fin policy tops = SOME (deploy_bc,runtime_bc) /\
      supported_program tops /\ supported_program_deploy tops /\
      deploy_typing_ok tops am tx /\
      deploy_state_rel tops deploy_bc am tx es /\
      LENGTH (call_trace es) < 2 ** 64 ==>
      ?r es'. run_call es = SOME (r,es') /\
        (creation_resource_starved es r es' \/
         deploy_call_result_rel tops runtime_bc am tx es r es')``;
    val expanded = concl (ASSUME expected);
  in
    if aconv expanded (concl savedDeploymentAdmission) then ()
    else raise Fail "PLAN 5.11 deployment schema mismatch"
  end;
