Theory gasFocusReplayExit
Ancestors
  asmOptimizer codegenEntrySim o1StaticPipelineCorrect o1PipelineCorrect
  o1StaticPipelineCompose o1CodeEndDftTransport o1CodeEndCfgNormTransport
  dftGasInvOracleFrame venomExecProofs contextRawReachable staticAbortDefs
  unitMemInv o1PassContract o1RequestContract venomPassSchedule
  o1DftStageSsa dftContractGas unitTransformDefs

Theorem replay_exit_raw_call_ctx[local]:
  !v C fn inst s. raw_reachable v C fn inst s ==> s.vs_call_ctx = v.vs_call_ctx
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (drule inv_enters_block_call_ctx >> simp[])
  >- (drule step_inst_ok_preserves_call_ctx >> simp[])
  >- metis_tac[inv_enters_block_call_ctx, step_inst_ok_preserves_call_ctx] >>
  metis_tac[inv_enters_block_call_ctx, inv_setup_callee_call_ctx]
QED

Theorem replay_exit_lowered_nonstatic[local]:
  ~vs.vs_call_ctx.cc_static /\
  (?eom. max_live_eom C = SOME eom /\
    mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
      lowered_mem_fact eom ctx fn inst s) C vs) ==>
  o1_lowered_inv C vs
Proof
  rw[o1_lowered_inv_def, mem_inv_raw_reachable] >>
  qexists `eom` >> simp[] >> rpt strip_tac >>
  drule_then assume_tac replay_exit_raw_call_ctx >>
  first_x_assum drule >> simp[in_static_abort_prefix_def]
QED

(* Both compiler simulations meet at the same C7 context and gas filling. *)
Theorem focus_v3_exit_from_replay:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\ o1_run_state_ok vs0 /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n fmp /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  dead_wf D /\
  o1_pre_walk_inv D unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  (fin = asm_opt_finalizer ==>
    (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
       ~MEM (Label "code_end") inst.inst_operands) /\
    LENGTH vs0.vs_data_section < dimword (:256) DIV 2 /\
    mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
      s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
      unit.cu_context
      (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 7) (vs0 with vs_gas_readings := raw ++ [0w]))
     (ev_context orc fuel (stage 7) vs0)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 8) vs0) (ev_context orc fuel (stage 8) vs0)) /\
  (!p d fn inst s. ev_reachable orc vs0 (stage 7) p d fn inst s ==>
     ?ws. raw_reachable (vs0 with vs_gas_readings := raw ++ [0w])
       (stage 7) fn inst (s with vs_gas_readings := ws)) /\
  (!fn inst s. raw_reachable vs0 (stage 8) fn inst s ==>
     ?p d. ev_reachable orc vs0 (stage 8) p d fn inst
       (s with vs_gas_readings := vs0.vs_gas_readings)) ==>
  ctx_sim D unit.cu_context out.po_unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
  ctx_abort_rq D unit.cu_context out.po_unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) vs0 /\
  (fin = asm_opt_finalizer ==> code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context) /\
  o1_lowered_inv out.po_unit.cu_context vs0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
   code_layout_valid vs0 /\ ~vs0.vs_call_ctx.cc_static` by fs[o1_run_state_ok_def] >>
  `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp` by fs[codegen_asm_entry_rel_def] >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0` by
    (rewrite_tac[fmp_variant_room_def] >>
     conj_tac >- metis_tac[generate_context_plan_eom_room] >> first_assum ACCEPT_TAC) >>
  `LENGTH o1_fn_passes = 9` by EVAL_TAC >>
  `!k. k <= 9 ==> o1_ctx_shape (stage k)` by metis_tac[] >>
  `!k. k <= 9 ==> EVERY (o1_fn_row k) (stage k).ctx_functions` by metis_tac[] >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  qpat_assum `!k. k < 9 ==> ctx_pass_stage _ _ _ _ _`
    (fn th => map_every (fn k =>
      qspec_then k (assume_tac o SIMP_RULE (srw_ss()) [o1_fn_passes_def]) th) [`7`,`8`]) >>
  `o1_ctx_shape (stage 7) /\ o1_ctx_shape (stage 8)` by simp[] >>
  qabbrev_tac `vi = vs0 with
    <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `vi = ((vs0 with vs_gas_readings := raw ++ [0w]) with
    <|vs_fmp := fmp; vs_initial_fmp := fmp|>)` by simp[Abbr `vi`] >>
  `o1_pre_walk_inv D unit.cu_context
    ((vs0 with vs_gas_readings := raw ++ [0w]) with
     <|vs_fmp := fmp; vs_initial_fmp := fmp|>)` by metis_tac[] >>
  qpat_assum `LENGTH o1_fn_passes = 9` (fn th =>
    drule_all (REWRITE_RULE [th] o1_pipeline_pre_dft_source_facts_static_abort_fixed)) >>
  qpat_assum `vi = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  strip_tac >>
  `o1_lowered_inv (stage 7) (vs0 with vs_gas_readings := raw ++ [0w]) /\
   EVERY wf_ssa (stage 7).ctx_functions` by
    (qpat_x_assum `o1_inv D 7 _ _` mp_tac >> simp[NoAsms, o1_inv_def, o1_ssa_inv_def]) >>
  `(vs0.vs_call_ctx.cc_static ==>
    !fn inst l. MEM fn (stage 7).ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
      l IN FDOM vs0.vs_labels)` by simp[] >>
  drule_all o1_walk_dft_exit_static_abort_fixed >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  conj_tac
  >- (irule ctx_sim_fuel_imp_ctx_sim >>
      qexists `cfg_norm_fuel (stage 9) o I` >>
      qpat_assum `stage 9 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      irule ctx_sim_fuel_trans >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`stage 7`, `vs0 with vs_gas_readings := raw ++ [0w]`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `stage 9 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      irule ctx_abort_rq_trans >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`stage 7`, `vs0 with vs_gas_readings := raw ++ [0w]`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac >- metis_tac[replay_exit_lowered_nonstatic] >>
  strip_tac >> qpat_x_assum `fin = asm_opt_finalizer ==> _` drule >> strip_tac >>
  `vi.vs_code = vs0.vs_code /\ vi.vs_data_section = vs0.vs_data_section` by
    simp[Abbr `vi`, IgnAsm `vi = _`] >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
      s.vs_code = vi.vs_code /\ s.vs_data_section = vi.vs_data_section)
    unit.cu_context vi` by
    (qpat_assum `vi.vs_code = _` SUBST1_TAC >>
     qpat_assum `vi.vs_data_section = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `v7 = vs0 with vs_gas_readings := raw ++ [0w]` >>
  `v7 = (vs0 with vs_gas_readings := raw ++ [0w])` by simp[Abbr `v7`] >>
  `code_end_offset_ok (raw_reachable v7) (stage 7)` by
    (qpat_assum `LENGTH o1_fn_passes = 9` (fn th =>
       drule_all (REWRITE_RULE [th] o1_pipeline_pre_dft_raw_code_end_offset_fixed)) >>
     disch_then ACCEPT_TAC) >>
  drule_all dft_stage_fn_rel >> strip_tac >>
  `ctx_labels_bound (stage 7) vs0.vs_labels` by (irule dft_ctx_labels_bound >> simp[]) >>
  `EVERY wf_ssa (stage 8).ctx_functions` by (drule_all dft_stage_wf_ssa >> simp[]) >>
  qpat_x_assum `v7 = _` SUBST_ALL_TAC >>
  drule_all dft_fixed_filling_code_end_offset_ok >> strip_tac >>
  qpat_assum `o1_initial_state_ok vs0`
    (strip_assume_tac o REWRITE_RULE [o1_initial_state_ok_def]) >>
  qpat_assum `stage 9 = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
  drule_all (cfg_norm_code_end_offset_ok |> Q.INST [`guarded` |-> `F`]
    |> REWRITE_RULE [] |> CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  disch_then ACCEPT_TAC
QED
