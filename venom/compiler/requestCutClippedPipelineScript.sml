Theory requestCutClippedPipeline
Ancestors
  requestCutClippedSafety requestCutOracleClip requestCutOracleReplay
  e2eRequestCutDefs o1StaticPipelineCorrect o1CodeEndWalkCompose
  o1CodeEndSourceTransport o1PipelineCorrect o1PipelineCompose
  o1PassContract o1ComposeSupport o1ContractSimplifyCfg
  venomPassSchedule venomPipelineRunner irSupply fcgPruning unitShapeDefs
  unitMemInv unitTransformDefs lowerDloadDefs memSafeRun codegenSymRel
  contextRawReachable contextCodegenRel jointRequestCut dftGasOracleFromList
  dftGasFromListRestore dftGasToListReachWitness dftGasToListAbort dftGasOracleDefs
  o1SafeUpto o1RequestContract crossBlockSimProps passSimulationDefs
  venomExecSemantics venomWf venomState venomInst finite_map list words

Theorem request_cut_clipped_abort:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\f. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
    f.fn_blocks) C.ctx_functions /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  LENGTH s.vs_requests = k /\ step_inst fuel C inst s = OK t /\
  k < LENGTH t.vs_requests ==>
  ?n u. run_context n C (vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests)
      vs.vs_outcomes) = Abort ExHalt_abort u /\ u.vs_requests = s.vs_requests
Proof
  strip_tac >>
  `LENGTH s.vs_requests <= k /\ LENGTH s.vs_requests < LENGTH t.vs_requests` by simp[] >>
  drule_all step_inst_request_outcomes >> strip_tac >>
  `inst.inst_opcode <> GAS` by fs[MEM] >>
  drule_all raw_reachable_outcome_clip >> simp[] >> strip_tac >>
  qabbrev_tac `clip_entry = vs with vs_outcomes := TAKE (k - LENGTH vs.vs_requests) vs.vs_outcomes` >>
  qabbrev_tac `clip_pre = s with vs_outcomes := []` >>
  qabbrev_tac `clip_abort = halt_state (set_returndata [] clip_pre)` >>
  `step_inst_base inst clip_pre = Abort ExHalt_abort clip_abort` by
    (drule_all external_ok_empty_oracle_abort >> simp[Abbr `clip_pre`, Abbr `clip_abort`]) >>
  mp_tac (Q.INST [`ctx` |-> `C`, `s` |-> `clip_entry`] gas_oracle_from_list) >>
  simp[] >> disch_then (qx_choose_then `orc` strip_assume_tac) >>
  `raw_reachable clip_entry C fn inst clip_pre` by simp[Abbr `clip_entry`, Abbr `clip_pre`] >>
  qpat_assum `!fn inst t. raw_reachable clip_entry C fn inst t ==> _` drule >>
  disch_then (qx_choosel_then [`p`, `d`] assume_tac) >>
  drule ev_reachable_trace_item >> simp[] >>
  disch_then (qx_choose_then `n` assume_tac) >>
  `step_inst_base inst (clip_pre with vs_gas_readings := clip_entry.vs_gas_readings) =
    Abort ExHalt_abort (clip_abort with vs_gas_readings := clip_entry.vs_gas_readings)` by
    (mp_tac (Q.INST [`gs` |-> `clip_entry.vs_gas_readings`, `s` |-> `clip_pre`, `inst` |-> `inst`]
       step_base_restore) >>
     Cases_on `step_inst_base inst (clip_pre with vs_gas_readings := clip_entry.vs_gas_readings)` >>
     simp[restore_rel_def]) >>
  drule_all trace_context_primitive_abort >> strip_tac >>
  qpat_assum `!fuel. gas_res_rel _ _` (qspec_then `n` mp_tac) >>
  namedCases_on `run_context n C clip_entry` ["", "", "ab u", "", ""] >>
  simp[gas_res_rel_def] >> strip_tac >>
  qpat_x_assum `gas_variant _ _` (mp_tac o REWRITE_RULE [gas_variant_def]) >>
  disch_then (mp_tac o Q.AP_TERM `\v. v.vs_requests`) >>
  simp[Abbr `clip_abort`, Abbr `clip_pre`, halt_state_def, set_returndata_def] >> strip_tac >>
  qexistsl_tac [`n`, `u`] >> gvs[]
QED

(* The source and stage-7 runs use the same clipped outcome oracle. The
   gas readings and raw FMP are the ones from the selected filling. *)
Theorem request_cut_clipped_pre_dft_facts:
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,supply) /\ pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
  (!j. j < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL j o1_fn_passes) (o1_walk_view rp j) (stage j) (stage (SUC j))) /\
  (!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)) /\
  (!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) (stage j).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\ fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0 /\
  v7 = (vs0 with <|vs_outcomes := short; vs_gas_readings := rds|>) /\
  vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  o1_pre_walk_inv D unit.cu_context vi /\
  (guarded ==>
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
    mem_inv (\ctx fn i s. inst_dload_in_section i s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section) unit.cu_context vi /\
    (!fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
      ~MEM (Label "code_end") i.inst_operands)) ==>
  ctx_sim_fuel I D unit.cu_context (stage 7) vi v7 /\
  ctx_abort_rq D unit.cu_context (stage 7) vi v7 /\
  o1_inv D 0 (stage 0) vi /\
  o1_lowered_inv (stage 7) v7 /\
  (guarded ==> code_end_offset_ok (raw_reachable v7) (stage 7))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `clip_entry = vs0 with vs_outcomes := short` >>
  `v7 = (clip_entry with vs_gas_readings := rds)` by simp[Abbr `clip_entry`] >>
  `code_layout_valid clip_entry` by
    (qpat_assum `code_layout_valid vs0` (mp_tac o REWRITE_RULE [code_layout_valid_def]) >>
     simp[Abbr `clip_entry`, code_layout_valid_def]) >>
  `o1_initial_state_ok clip_entry /\ clip_entry.vs_fmp = clip_entry.vs_initial_fmp /\
   fmp_variant_room (SOME fmp) out.po_unit.cu_context clip_entry` by
    fs[Abbr `clip_entry`, o1_initial_state_ok_def, fmp_variant_room_def] >>
  mp_tac (Q.INST [`rpolicy` |-> `rp`, `stage` |-> `stage`, `D` |-> `D`,
    `unit` |-> `unit`, `out` |-> `out`, `pre` |-> `pre`, `t` |-> `supply`,
    `entry` |-> `entry`, `vs_out` |-> `clip_entry`, `rds` |-> `rds`, `fmp` |-> `fmp`]
    o1_pipeline_pre_dft_source_facts_static_abort_fixed) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC [LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >>
  qpat_assum `v7 = (clip_entry with vs_gas_readings := rds)`
    (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  qpat_assum `vi = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `o1_lowered_inv (stage 7) v7` by fs[o1_inv_def, o1_ssa_inv_def] >>
  simp[] >> strip_tac >>
  qpat_x_assum `guarded ==> _` mp_tac >> simp[] >> strip_tac >>
  `unit_wf unit /\ ALL_DISTINCT (unit_label_namespace unit)` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
      (mp_tac o MATCH_MP o1_driver_runs o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     simp[]) >>
  `o1_ctx_shape unit.cu_context /\ ir_supply_inst_ok (init_ir_supply unit)` by
    simp[init_ir_supply_inst_ok, o1_source_unit_ok_ctx_shape] >>
  `vi.vs_vars = FEMPTY /\ ~vi.vs_halted /\ LENGTH clip_entry.vs_data_section < dimword (:256) DIV 2` by
    fs[Abbr `clip_entry`, o1_initial_state_ok_def] >>
  `EVERY simplify_cfg_fn_ok unit.cu_context.ctx_functions /\
   EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) unit.cu_context.ctx_functions` by
    (fs[o1_pre_walk_inv_def, o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[o1_fn_shape_def, SRULE [EVERY_MEM] simplify_cfg_fn_ok_no_phi]) >>
  `EVERY make_ssa_input_ok (stage 0).ctx_functions` by fs[o1_inv_def, o1_walk_src_inv_def] >>
  qpat_assum `!j. j < LENGTH _ ==> _`
    (qspec_then `0` (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def])) >>
  mp_tac (Q.INST [`C1` |-> `stage 1`, `fcg` |-> `fcg_analyze pre.cu_context`,
    `vs` |-> `vi`, `view` |-> `o1_walk_view rp 0`, `rp` |-> `rp`,
    `supply` |-> `init_ir_supply unit`, `supply'` |-> `supply`]
    code_end_source_prefix_transport) >>
  qpat_assum `stage 0 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >> strip_tac >>
  `fmp_variant_room (SOME fmp) (stage (LENGTH o1_fn_passes)) clip_entry` by simp[] >>
  drule_all o1_code_end_pre_dft_bound_fixed >>
  simp[]
QED

Theorem clipped_invariants_request_cut:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  EVERY wf_function C.ctx_functions /\
  clipped = (v with vs_outcomes := TAKE (k - LENGTH v.vs_requests) v.vs_outcomes) /\
  o1_lowered_inv C clipped /\
  (guarded ==> code_end_offset_ok (raw_reachable clipped) C) ==>
  (?eom. max_live_eom C = SOME eom /\
    mem_inv (\ctx fn i s. request_cut k s ==> lowered_mem_fact eom ctx fn i s) C v) /\
  (guarded ==> code_end_offset_ok
    (\ctx fn i s. raw_reachable v ctx fn i s /\ request_cut k s) C)
Proof
  strip_tac >>
  `!fn i s. raw_reachable v C fn i s /\ request_cut k s ==>
    raw_reachable clipped C fn i
      (s with vs_outcomes := TAKE (k - LENGTH s.vs_requests) s.vs_outcomes)` by
    (simp[request_cut_def] >> metis_tac[raw_reachable_outcome_clip]) >>
  fs[o1_lowered_inv_def, mem_inv_raw_reachable] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!fn i s. raw_reachable v C fn i s /\ request_cut k s ==> _`
        drule_all >> strip_tac >>
      qpat_x_assum `!fn i s. raw_reachable _ C fn i s ==> lowered_mem_fact _ C fn i s`
        drule >> simp[lowered_mem_fact_def, lowered_mem_ok_def, in_revert_forward_def,
                      inst_mem_ranges_def]) >>
  strip_tac >> fs[code_end_offset_ok_def] >> rpt strip_tac >>
  qpat_x_assum `!fn i s. raw_reachable v C fn i s /\ request_cut k s ==> _`
    drule_all >> strip_tac >>
  qpat_x_assum `!fn i s dst x sz w base. raw_reachable _ C fn i s /\ _ ==> _` drule >>
  simp[] >> metis_tac[]
QED

Theorem request_cut_pre_dft:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  o1PipelineCorrect$o1_pipeline rp unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\ unit_defs_reach_uses unit /\
  run_pipeline_stages rp o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,supply) /\ pre.cu_context.ctx_entry = SOME entry /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage (LENGTH o1_fn_passes) = out.po_unit.cu_context /\
  (!j. j < LENGTH o1_fn_passes ==>
    ctx_pass_stage rp (EL j o1_fn_passes) (o1_walk_view rp j) (stage j) (stage (SUC j))) /\
  (!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)) /\
  (!j. j <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row j) (stage j).ctx_functions) /\
  dead_wf D /\ o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\ fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0 /\
  unit.cu_context.ctx_entry = SOME entry /\
  lookup_function entry unit.cu_context.ctx_functions = SOME entryfn /\
  fn_entry_label entryfn = SOME lbl /\
  w7 = (vs0 with vs_gas_readings := rds) /\
  w = (w7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  raw_safe_rq_upto D 0 k unit.cu_context w /\ o1_safe_upto Ds reserve n unit.cu_context w /\
  raw_reachable w unit.cu_context fn i s /\ LENGTH s.vs_requests = k /\
  short = TAKE (k - LENGTH vs0.vs_requests) vs0.vs_outcomes /\
  vi = (w with vs_outcomes := short) /\ v7 = (w7 with vs_outcomes := short) /\
  (guarded ==>
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
    !fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
      ~MEM (Label "code_end") i.inst_operands) ==>
  ctx_abort_rq D unit.cu_context (stage 7) vi v7 /\
  o1_inv D 0 (stage 0) vi /\
  (?eom. max_live_eom (stage 7) = SOME eom /\
    mem_inv (\ctx fn i s. request_cut k s ==> lowered_mem_fact eom ctx fn i s) (stage 7) w7) /\
  (guarded ==> code_end_offset_ok
    (\ctx fn i s. raw_reachable w7 ctx fn i s /\ request_cut k s) (stage 7))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `unit_wf unit` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
      (mp_tac o MATCH_MP o1_driver_runs o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     simp[]) >>
  `o1_ctx_shape unit.cu_context` by simp[o1_source_unit_ok_ctx_shape] >>
  `vi = (w with vs_outcomes := TAKE (k - LENGTH w.vs_requests) w.vs_outcomes)` by simp[] >>
  drule_all request_cut_source_pre_walk >> strip_tac >>
  `v7 = (vs0 with <|vs_outcomes := short; vs_gas_readings := rds|>) /\
   vi = (v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>)` by simp[] >>
  `vi.vs_code = w.vs_code /\ vi.vs_data_section = w.vs_data_section` by simp[] >>
  `guarded ==> LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
    mem_inv (\ctx fn i s. inst_dload_in_section i s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section) unit.cu_context vi /\
    !fn i. MEM fn unit.cu_context.ctx_functions /\ MEM i (fn_insts fn) ==>
      ~MEM (Label "code_end") i.inst_operands` by
    (strip_tac >> qpat_assum `guarded ==> _` drule >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `vi.vs_code = w.vs_code` (fn code_eq =>
           qpat_assum `vi.vs_data_section = w.vs_data_section` (fn data_eq =>
             PURE_REWRITE_TAC [code_eq, data_eq])) >>
         first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  drule_all request_cut_clipped_pre_dft_facts >> strip_tac >> simp[] >>
  `7 <= LENGTH o1_fn_passes` by simp[o1_fn_passes_def] >>
  `o1_ctx_shape (stage 7)` by
    (qpat_assum `!j. j <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage j)`
       (qspec_then `7` mp_tac) >> simp[]) >>
  `EVERY wf_function (stage 7).ctx_functions` by
    (fs[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def] >> metis_tac[]) >>
  `v7 = (w7 with vs_outcomes := TAKE (k - LENGTH w7.vs_requests) w7.vs_outcomes)` by simp[] >>
  drule_all clipped_invariants_request_cut >> simp[]
QED

(* The two retained visits exhaust the clipped oracle after the same number
   of requests. The pre-DFT abort relation then compares the whole prefix. *)
Theorem clipped_abort_request_history:
  ctx_abort_rq D C C' vi v7 /\ run_context m C vi = Abort a s /\
  run_context n C' v7 = Abort b t /\ LENGTH s.vs_requests = LENGTH t.vs_requests ==>
  LIST_REL (request_agree_except D) s.vs_requests t.vs_requests
Proof
  strip_tac >> fs[ctx_abort_rq_def] >>
  qpat_x_assum `!fuel a t. run_context fuel C vi = Abort a t ==> _` drule >>
  disch_then (qx_choosel_then [`n'`, `b'`, `t'`] strip_assume_tac) >>
  `run_context n C' v7 = run_context n' C' v7` by
    (Cases_on `C'.ctx_entry` >> fs[run_context_def] >>
     rename1 `C'.ctx_entry = SOME entry` >>
     Cases_on `lookup_function entry C'.ctx_functions` >> fs[] >>
     rename1 `lookup_function entry C'.ctx_functions = SOME f` >>
     Cases_on `fn_entry_label f` >> fs[run_function_def] >>
     rename1 `fn_entry_label f = SOME label` >>
     qspecl_then [`n`, `n'`, `C'`, `f`,
       `v7 with <|vs_prev_bb := NONE; vs_current_bb := label; vs_inst_idx := 0|>`]
       mp_tac run_blocks_deterministic >>
     simp[terminates_def]) >>
  gvs[request_prefix_rel_EL, LIST_REL_EL_EQN]
QED
