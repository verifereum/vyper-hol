Theory gasFocusStaticReplay
Ancestors
  gasFocusStaticCodeEndSeam gasFocusStaticExitLift
  o1StaticPipelineCorrect o1StaticPipelineCompose
  o1PassContract o1RequestContract o1PassLift o1PipelineCorrect
  o1PipelineCompose o1ComposeSupport o1LabelStages venomPassSchedule
  codegenEntryRel codegenEntrySim asmOptimizer
  dftGasOracleDefs dftWaveStaticGasContract
  contextRawReachable unitMemInv staticAbortDefs memSafeRun
  irSupply fcgPruning fcgDefs venomWf list rich_list finite_map words arithmetic

(* Close the static pipeline at one raw filling and its stage-7/8 oracle. *)
Theorem focus_static_replay_exit_for:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands) /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\
  (fin = asm_opt_finalizer ==>
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (?fr. terminates (run_context fr unit.cu_context
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
  dead_wf D /\
  o1_pre_walk_inv D unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  (fin = asm_opt_finalizer ==>
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
               s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
       unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 7)
    (vs0 with vs_gas_readings := raw ++ [0w]))
    (ev_context orc fuel (stage 7) vs0)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 8) vs0)
    (ev_context orc fuel (stage 8) vs0)) /\
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
  (fin = asm_opt_finalizer ==>
     code_end_offset_ok
       (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
         ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
  ((o1_lowered_inv out.po_unit.cu_context vs0 /\
    (fin = asm_opt_finalizer ==>
       code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
   ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
      mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
        out.po_unit.cu_context vs0) /\
    !fuel. terminates (run_context fuel unit.cu_context
              (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
           ?u. run_context fuel unit.cu_context
                 (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
               Abort ExHalt_abort u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `rds = raw ++ [0w]` >>
  qabbrev_tac `v7 = vs0 with vs_gas_readings := rds` >>
  qabbrev_tac `vi = v7 with <|vs_fmp := fmp; vs_initial_fmp := fmp|>` >>
  `vi = (vs0 with <|vs_gas_readings := rds; vs_fmp := fmp;
                  vs_initial_fmp := fmp|>)` by simp[Abbr `vi`, Abbr `v7`, Abbr `rds`] >>
  map_every (fn q => qpat_assum q (fn th =>
    let val eq = GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)
    in RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >>
       PURE_REWRITE_TAC [eq] >> assume_tac th
    end))
    [`Abbrev (rds = _)`, `Abbrev (v7 = _)`, `vi = _`] >>
  `fmp_variant_room (SOME fmp) out.po_unit.cu_context vs0` by
    (simp[fmp_variant_room_def] >>
     qspecl_then [`out.po_unit.cu_context`, `cpl`, `vs0`] mp_tac
       generate_context_plan_eom_room >> simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  qpat_assum `!k. k <= 9 ==> _`
    (map_every assume_tac o CONJUNCTS o
      CONV_RULE (BINDER_CONV (REWR_CONV IMP_CONJ_THM) THENC FORALL_AND_CONV)) >>
  mp_tac (Q.INST [`rpolicy` |-> `rpolicy`, `stage` |-> `stage`,
    `D` |-> `D`, `unit` |-> `unit`, `out` |-> `out`, `pre` |-> `pre`,
    `t` |-> `t`, `entry` |-> `nm`, `vs_out` |-> `vs0`, `rds` |-> `rds`, `fmp` |-> `fmp`]
      o1_pipeline_pre_dft_sim_static_abort_fixed) >>
  qpat_assum `LENGTH o1_fn_passes = 9` (fn th => PURE_REWRITE_TAC [th]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (v7 = _)`
    (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `Abbrev (vi = _)`
    (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `o1_lowered_inv (stage 7) v7 /\ EVERY wf_ssa (stage 7).ctx_functions` by
    fs[o1_inv_def, o1_ssa_inv_def] >>
  `unit_wf unit /\ ALL_DISTINCT (unit_label_namespace unit)` by
    (qpat_assum `o1PipelineCorrect$o1_pipeline _ _ = _`
        (mp_tac o MATCH_MP o1_driver_runs o REWRITE_RULE [o1PipelineCorrectTheory.o1_pipeline_def]) >>
     simp[]) >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `!fn inst. MEM fn pre.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    (mp_tac (Q.INST [`rpolicy` |-> `rpolicy`, `s` |-> `init_ir_supply unit`,
                     `s'` |-> `t`, `unit` |-> `unit`, `unit'` |-> `pre`]
               o1_pre_walk_no_runtime_begin) >>
     (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[init_ir_supply_inst_ok]))) >>
     disch_then ACCEPT_TAC) >>
  `!fn inst. MEM fn (stage 0).ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    (gvs[prune_unit_fcg_unreachable_def] >> fs[MEM_FILTER] >> metis_tac[]) >>
  `!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) any_view
    (stage k) (stage (SUC k))` by
    (gen_tac >> disch_tac >>
     qpat_assum `!k. k < 9 ==> ctx_pass_stage _ _ (o1_walk_view _ _) _ _`
       (qspec_then `k` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE [ctx_pass_stage_def]) >>
     simp[ctx_pass_stage_def, any_view_def] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     BETA_TAC >> rpt gen_tac >>
     disch_then (qx_choosel_then [`observed`, `supply`, `output`] strip_assume_tac) >>
     map_every qexists_tac [`observed`, `supply`, `output`] >> simp[]) >>
  `!fn inst. MEM fn (stage 7).ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands` by
    (mp_tac (Q.INST [`n` |-> `9`, `passes` |-> `o1_fn_passes`,
        `rpolicy` |-> `rpolicy`, `stage` |-> `stage`] o1_stage_chain_no_runtime_begin) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (qspec_then `7` mp_tac) >> simp[]) >>
  map_every (fn k =>
    (qpat_assum `!k. k <= 9 ==> o1_ctx_shape (stage k)`
       (qspec_then k (assume_tac o SRULE [])) >>
     qpat_assum `!k. k <= 9 ==> EVERY (o1_fn_row k) _`
       (qspec_then k (assume_tac o SRULE [])) >>
     qpat_assum `!k. k < 9 ==> ctx_pass_stage _ _ any_view _ _`
       (qspec_then k (assume_tac o SRULE [o1_fn_passes_def])))) [`7`, `8`] >>
  `o1_pre 7 (stage 7) (stage 8)` by simp[o1_pre_def] >>
  `!fn inst l. MEM fn (stage 7).ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode = CODECOPY /\ MEM (Label l) inst.inst_operands ==>
    l IN FDOM vs0.vs_labels` by
    (mp_tac (Q.INST [`C` |-> `stage 7`, `vs` |-> `vs0`] o1_runtime_codecopy_labels_bound) >>
     (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  mp_tac (Q.INST [`C7` |-> `stage 7`, `C8` |-> `stage 8`, `C9` |-> `stage 9`,
    `dft_view` |-> `any_view`, `cfg_view` |-> `any_view`,
    `D` |-> `D`, `vs_out` |-> `vs0`, `rp` |-> `rpolicy`,
    `rds` |-> `rds`, `orc` |-> `orc`] o1_walk_dft_exit_static_abort_fixed) >>
  qpat_assum `Abbrev (v7 = _)`
    (fn th => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  (impl_tac >- (rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE (disch_tac >> first_assum ACCEPT_TAC)))) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  imp_res_tac ctx_sim_fuel_imp_ctx_sim >>
  drule_all_then (map_every assume_tac o CONJUNCTS) (Q.INST [`A` |-> `unit.cu_context`,
    `B` |-> `stage 7`, `C` |-> `stage 9`,
    `a` |-> `vi`, `b` |-> `v7`, `c` |-> `vs0`, `D` |-> `D`]
      focus_static_exit_lift) >>
  qpat_assum `stage 9 = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> assume_tac th) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  map_every (fn q => qpat_assum q
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (rds = _)`, `Abbrev (v7 = _)`, `Abbrev (vi = _)`] >>
  mp_tac (Q.INST [`orc` |-> `orc`, `stage` |-> `stage`, `pre` |-> `pre`, `t` |-> `t`]
    focus_static_selected_code_end_exit_for) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (disch_tac >>
     qpat_assum `fin = asm_opt_finalizer ==> (!fn inst. _ ==> ~MEM (Label "code_end") _) /\ _`
       (fn th => drule th >> strip_tac) >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[]))))) >>
  disch_then ACCEPT_TAC
QED

Theorem focus_static_replay_exit:
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
  code_layout_valid vs0 /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "runtime_begin") inst.inst_operands) /\
  generate_context_plan out.po_unit.cu_context = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  w2n vs0.vs_initial_fmp <= w2n fmp /\
  (fin = asm_opt_finalizer ==>
     (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                ~MEM (Label "code_end") inst.inst_operands) /\
     LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
    (init_ir_supply unit) = SOME (pre,t) /\
  pre.cu_context.ctx_entry = SOME nm /\
  stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
  stage 9 = out.po_unit.cu_context /\
  (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
    (stage k) (stage (SUC k))) /\
  (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
    EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  (?fr. terminates (run_context fr unit.cu_context
     (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>))) /\
  dead_wf D /\
  o1_pre_walk_inv D unit.cu_context
    (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
  (fin = asm_opt_finalizer ==>
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
               s.vs_code = vs0.vs_code /\ s.vs_data_section = vs0.vs_data_section)
       unit.cu_context (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 7)
    (vs0 with vs_gas_readings := raw ++ [0w]))
    (ev_context orc fuel (stage 7) vs0)) /\
  (!fuel. gas_res_rel (run_context fuel (stage 8) vs0)
    (ev_context orc fuel (stage 8) vs0)) /\
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
  (fin = asm_opt_finalizer ==>
     code_end_offset_ok
       (\ctx fn inst s. raw_reachable vs0 ctx fn inst s /\
         ~in_static_abort_prefix fn s) out.po_unit.cu_context) /\
  ((o1_lowered_inv out.po_unit.cu_context vs0 /\
    (fin = asm_opt_finalizer ==>
       code_end_offset_ok (raw_reachable vs0) out.po_unit.cu_context)) \/
   ((?eom. max_live_eom out.po_unit.cu_context = SOME eom /\
      mem_inv (\ctx fn inst s. in_static_abort_prefix fn s \/
                lowered_mem_ok eom (w2n s.vs_initial_fmp) ctx fn inst s)
        out.po_unit.cu_context vs0) /\
    !fuel. terminates (run_context fuel unit.cu_context
              (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>)) ==>
           ?u. run_context fuel unit.cu_context
                 (vs0 with <|vs_gas_readings := raw ++ [0w]; vs_fmp := fmp; vs_initial_fmp := fmp|>) =
               Abort ExHalt_abort u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp` by fs[codegen_asm_entry_rel_def] >>
  MATCH_MP_TAC focus_static_replay_exit_for >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
