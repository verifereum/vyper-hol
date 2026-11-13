Theory o1LabelFlowSource
Ancestors
  o1LabelFlowSourcePreWalk o1LabelFlowSourceSsaStep o1LabelFlowSourceBoundary
  o1PipelineCompose
  o1ScheduleDecomp o1PartialSchedule o1FnScheduleDecompHelpers
  o1ComposeSupport venomPassSchedule list irSupply venomPipelineRunner fcgPruning

Theorem rows_step_contract_enrich_after_first:
  0 < k /\ rows_step_contract o1_fn_row k rp pass ==>
  rows_step_contract (\j f. o1_fn_row j f /\ (j <= 1 ==> P f)) k rp pass
Proof
  simp[rows_step_contract_def] >> rpt strip_tac >>
  `EVERY (\g. ?j. o1_fn_row j g) observed.cu_context.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem rows_step_contracts_enrich_tail:
  !passes k. 0 < k /\ rows_step_contracts_from o1_fn_row rp k passes ==>
  rows_step_contracts_from (\j f. o1_fn_row j f /\ (j <= 1 ==> P f)) rp k passes
Proof
  Induct >> simp[rows_step_contracts_from_def] >> rpt strip_tac
  >- (irule rows_step_contract_enrich_after_first >> simp[])
  >> first_x_assum irule >> simp[]
QED

Theorem first_make_ssa_enriched_contract:
  rows_step_contract o1_fn_row 0 rp (CFP_Simple VP_MakeSSA) ==>
  rows_step_contract
    (\k f. o1_fn_row k f /\ (k <= 1 ==>
      ((!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
       (!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE /\
         (i.inst_opcode = CODECOPY ==>
          ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])))))
    0 rp (CFP_Simple VP_MakeSSA)
Proof
  rewrite_tac[rows_step_contract_def] >> disch_tac >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `EVERY (\g. ?j. o1_fn_row j g) observed.cu_context.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  drule_all first_make_ssa_step_seed_free_flow >> simp[]
QED

Theorem o1_source_enriched_contracts:
  rows_step_contracts_from
    (\k f. o1_fn_row k f /\ (k <= 1 ==>
      ((!i. MEM i (fn_insts f) ==> ~MEM (Label "code_end") i.inst_operands) /\
       (!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE /\
         (i.inst_opcode = CODECOPY ==>
          ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])))))
    rp 0 o1_fn_passes
Proof
  mp_tac (Q.SPEC `rp` (GEN_ALL o1_fn_passes_steps)) >>
  rewrite_tac[o1_fn_passes_def] >>
  disch_then (mp_tac o MATCH_MP o1_step_contracts_from_rows) >>
  rewrite_tac[Once rows_step_contracts_from_def] >> strip_tac >>
  rewrite_tac[Once rows_step_contracts_from_def] >> conj_tac
  >- (irule first_make_ssa_enriched_contract >> simp[]) >>
  ho_match_mp_tac rows_step_contracts_enrich_tail >> simp[]
QED

Theorem chain_facts_enriched_project:
  chain_facts (\k f. o1_fn_row k f /\ (k <= 1 ==> P f)) rp passes u names chains i ==>
  chain_facts o1_fn_row rp passes u names chains i
Proof
  simp[chain_facts_def] >> metis_tac[]
QED

Theorem o1_source_walk_decomp:
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s =
    SOME (u',s') /\ o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\
  (!f i. MEM f u.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands /\ i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
     ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])) ==>
  ?chains.
    LENGTH chains = LENGTH u.cu_context.ctx_functions /\
    (!i. i < LENGTH chains ==> chain_facts o1_fn_row rp o1_fn_passes u names chains i) /\
    u'.cu_context = stage_ctx u.cu_context chains (LENGTH o1_fn_passes) /\
    chains_ids_apart chains /\
    (!i. i < LENGTH chains ==>
      (!j. MEM j (fn_insts (EL 1 (FST (EL i chains)))) ==>
        ~MEM (Label "code_end") j.inst_operands /\ j.inst_opcode <> CODESIZE /\
        (j.inst_opcode = CODECOPY ==>
         ?dst sz. j.inst_operands = [dst; Label "runtime_begin"; sz])))
Proof
  strip_tac >>
  mp_tac o1_source_enriched_contracts >> disch_tac >>
  drule_at (Pos (el 1)) run_named_fn_schedules_decomp >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  impl_tac
  >- (simp[] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  disch_then (qx_choose_then `chains` strip_assume_tac) >>
  qexists_tac `chains` >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule chain_facts_enriched_project >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  qpat_x_assum `!i. i < LENGTH chains ==> chain_facts _ _ _ _ _ _ _`
    (qspec_then `i` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
  drule_at (Pos (el 1)) chain_facts_row >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[o1_fn_passes_def] >> metis_tac[]
QED

Theorem o1_pipeline_source_chains:
  run_venom_pipeline mem_ok calling_ok post_ok rp o1_pipeline_spec unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  label_flow_ok unit.cu_context /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  ?pre entry chains.
    pre.cu_context.ctx_entry = SOME entry /\ o1_ctx_shape pre.cu_context /\
    LENGTH chains = LENGTH
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context.ctx_functions /\
    (!i. i < LENGTH chains ==>
      chain_facts o1_fn_row rp o1_fn_passes
        (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context))
        (fcg_postorder (fcg_analyze pre.cu_context) entry) chains i) /\
    out.po_unit.cu_context = stage_ctx
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context
      chains (LENGTH o1_fn_passes) /\ chains_ids_apart chains /\
    (!i j. i < LENGTH chains /\ MEM j (fn_insts (EL 1 (FST (EL i chains)))) ==>
      ~MEM (Label "code_end") j.inst_operands /\ j.inst_opcode <> CODESIZE /\
      (j.inst_opcode = CODECOPY ==>
        ?dst sz. j.inst_operands = [dst; Label "runtime_begin"; sz])) /\
    (!i. i < LENGTH chains ==>
      label_flow_ok (pre.cu_context with ctx_functions := [EL 1 (FST (EL i chains))]))
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  drule o1_pre_walk_seed_free_flow >> simp[] >> disch_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `unit.cu_context.ctx_entry = SOME entry` by metis_tac[] >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_walk_callee_first) >> simp[] >> strip_tac >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `o1_ctx_shape (prune_unit_fcg_unreachable pre
     (fcg_analyze pre.cu_context)).cu_context /\
   ALL_DISTINCT (unit_label_namespace
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)))` by
    metis_tac[o1_ctx_shape_prune] >>
  fs[run_callee_first_def] >>
  drule o1_source_walk_decomp >> impl_tac
  >- (simp[o1_prune_every] >>
      metis_tac[MEM_prune_unit_fcg_unreachable_functions]) >>
  strip_tac >> qexistsl_tac [`pre`, `entry`, `chains`] >> simp[] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  metis_tac[label_flow_ok_seed_free_function]
QED
