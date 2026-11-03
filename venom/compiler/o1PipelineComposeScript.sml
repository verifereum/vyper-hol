(*
 * The O1 pipeline from its per-pass contracts.
 *
 * run_venom_pipeline is two pre-walk schedules (SimplifyCFG, DretDesugar
 * over every function), the pruning of unreachable functions, and the
 * callee-first walk of o1_fn_passes.  Each schedule decomposes into stage
 * contexts (o1ScheduleDecomp); each consecutive pair is one contract
 * theorem's instance (o1PassContract); pruning is a context agreement
 * (ctxLookupAgree).  Composing them gives o1_pipeline_stage_facts: the
 * output context's shape, a forward simulation from every initial state
 * that satisfies the raw memory invariant, and the lowered memory
 * invariant of the output.  o1PipelineCorrect states S4 and S6 from it.
 *
 * The gas form of the DFT contract is used through gas_variant being
 * equality: when SEQ-243's oracle makes it a real relation, the
 * composition and S4 take the forall-out exists-in form too.
 *)
Theory o1PipelineCompose
Ancestors
  o1ComposeSupport o1PassContract o1ContractTheorems o1ScheduleDecomp
  ctxLookupAgree unitMemInv
  unitTransformDefs unitShapeDefs venomPipelineDriver venomPipelineRunner
  venomPipelineRunnerProps venomFnScheduleRunner venomPassSchedule
  venomPassDispatcher venomCompilerWf venomWf venomInst venomExecSemantics
  venomState stateEquivProps fcgDefs fcgPruning fcgPostorder
  fcgAnalysisProps fcgBridge contextCodegenRel venomMemDefs list rich_list

(* ===== Simulations compose ===== *)

Theorem unit_result_rel_trans:
  unit_result_rel r1 r2 /\ unit_result_rel r2 r3 ==> unit_result_rel r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[unit_result_rel_def] >> metis_tac[observable_equiv_trans]
QED

Theorem ctx_sim_trans:
  ctx_sim C1 C2 s s /\ ctx_sim C2 C3 s s ==> ctx_sim C1 C3 s s
Proof
  rw[ctx_sim_def] >> first_x_assum drule >> strip_tac >>
  `terminates (run_context fuel' C2 s)` by
    metis_tac[unit_result_rel_terminates] >>
  first_x_assum drule >> strip_tac >>
  metis_tac[unit_result_rel_trans]
QED

Theorem ctx_sim_run_context_eq:
  ctx_sim C1 C2 s s /\ (!fuel. run_context fuel C2 s = run_context fuel C3 s)
  ==> ctx_sim C1 C3 s s
Proof
  simp[ctx_sim_def] >> metis_tac[]
QED

Theorem o1_stage_contract_gas_imp:
  o1_stage_contract_gas rpolicy pass view pre M M' ==>
  o1_stage_contract rpolicy pass view pre M M'
Proof
  rw[o1_stage_contract_gas_def, o1_stage_contract_def, gas_variant_def] >>
  metis_tac[]
QED

(* ===== The memory facts are range-wise ===== *)

Theorem rangewise_raw_mem_ok:
  rangewise_mem_fact raw_mem_ok
Proof
  simp[rangewise_mem_fact_def] >>
  qexistsl_tac [`\next allocas fmp. next < dimword (:256)`,
    `\r next allocas fmp. SND r = 0 \/ FST r + SND r <= next`] >>
  simp[raw_mem_ok_def, inst_mem_below_frontier_def, inst_mem_ranges_def,
       pairTheory.ELIM_UNCURRY]
QED

Theorem rangewise_mem_fact_ctx:
  rangewise_mem_fact M ==> (M ctx fn inst s <=> M ctx' fn' inst s)
Proof
  rw[rangewise_mem_fact_def] >> simp[]
QED

Theorem o1_fn_passes_steps:
  o1_step_contracts_from rp 0 o1_fn_passes
Proof
  simp[o1_fn_passes_def, o1_step_contracts_from_def,
       o1_contract_make_ssa_1, o1_contract_lower_dload,
       o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
       o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
       o1_contract_dft, o1_contract_cfg_normalization]
QED

Theorem o1_run_contracts:
  k < LENGTH o1_fn_passes ==> o1_run_contract rp k
Proof
  simp[o1_fn_passes_def] >> strip_tac >>
  `k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/
   k = 8` by decide_tac >>
  gvs[o1_contract_make_ssa_1, o1_contract_lower_dload,
      o1_contract_concretize_mem_loc, o1_contract_fmp_lowering,
      o1_contract_make_ssa_2, o1_contract_simplify_cfg, o1_contract_sue,
      o1_contract_cfg_normalization] >>
  simp[o1_run_contract_def] >> irule o1_stage_contract_gas_imp >>
  mp_tac (Q.INST [`rpolicy` |-> `rp`] o1_contract_dft) >>
  simp[o1_run_contract_gas_def]
QED

(* ===== Source shape ===== *)

Theorem o1_source_unit_ok_ctx_shape:
  unit_wf unit /\ o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
  unit_entry_no_params unit /\ unit_first_block_no_phi unit ==>
  o1_ctx_shape unit.cu_context
Proof
  strip_tac >> simp[o1_ctx_shape_def] >> conj_tac
  >- gvs[unit_wf_def, venom_wf_def] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all source_member_shape >> strip_tac >>
  simp[o1_fn_shape_def] >> rpt conj_tac
  >- gvs[unit_label_refs_ok_def, EVERY_MEM]
  >- metis_tac[source_entry_shape]
  >> strip_tac >> drule_all source_internal_shape >> simp[]
QED

(* ===== One pre-walk schedule ===== *)

(* A pass mapped over every function, keeping an invariant. *)
Theorem o1_mapped_pass_sim:
  o1_step_contract rpolicy pass /\
  (!view. o1_stage_contract rpolicy pass view no_pre stage_inv stage_inv) /\
  run_mapped_functions rpolicy pass unit s = SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  o1_ctx_shape unit'.cu_context /\ unit_labels_wf unit' /\
  ir_supply_inst_ok s' /\
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved /\
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  !vs. o1_run_state_ok vs /\ stage_inv unit.cu_context vs ==>
       ctx_sim unit.cu_context unit'.cu_context vs vs /\ stage_inv unit'.cu_context vs
Proof
  strip_tac >> drule_all mapped_pass_stage >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `any_view` mp_tac) >>
  simp[o1_stage_contract_def, no_pre_def] >>
  disch_then drule_all >> simp[]
QED

Theorem o1_pre_walk_sim:
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s ==>
  o1_ctx_shape unit'.cu_context /\ unit_labels_wf unit' /\
  ir_supply_inst_ok s' /\
  unit'.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved /\
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  !vs. o1_run_state_ok vs /\ o1_src_inv unit.cu_context vs ==>
       ctx_sim unit.cu_context unit'.cu_context vs vs /\
       o1_src_inv unit'.cu_context vs
Proof
  strip_tac >> drule o1_pre_walk_runs >> strip_tac >>
  `o1_ctx_shape mid.cu_context /\ unit_labels_wf mid /\
   ir_supply_inst_ok t /\
   mid.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
   mid.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved /\
   ctx_fn_names mid.cu_context = ctx_fn_names unit.cu_context /\
   !vs. o1_run_state_ok vs /\ o1_src_inv unit.cu_context vs ==>
     ctx_sim unit.cu_context mid.cu_context vs vs /\ o1_src_inv mid.cu_context vs` by
    (irule o1_mapped_pass_sim >> metis_tac[o1_contract_simplify_cfg_pre_walk]) >>
  drule unit_labels_wf_namespace >> strip_tac >>
  drule_at (Pos (el 3)) o1_mapped_pass_sim >>
  disch_then (qspec_then `o1_src_inv` mp_tac) >>
  impl_tac >- simp[o1_contract_dret_desugar_pre_walk] >>
  strip_tac >> simp[] >> rpt gen_tac >> strip_tac >>
  metis_tac[ctx_sim_trans]
QED

(* ===== Pruning ===== *)

Theorem o1_ctx_shape_prune:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context ==>
  o1_ctx_shape (prune_unit_fcg_unreachable unit fcg).cu_context /\
  (ALL_DISTINCT (unit_label_namespace unit) ==>
   ALL_DISTINCT (unit_label_namespace (prune_unit_fcg_unreachable unit fcg)))
Proof
  strip_tac >> conj_tac
  >- (simp[o1_ctx_shape_def] >> conj_tac
      >- metis_tac[ctx_wf_prune_unit_fcg_unreachable, o1_ctx_shape_wf] >>
      simp[EVERY_MEM] >> metis_tac[pruned_member_shape]) >>
  simp[unit_label_namespace_def, prune_unit_fcg_unreachable_def] >>
  metis_tac[namespace_filter_distinct]

QED

Theorem o1_prune_sim:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\ rangewise_mem_fact M ==>
  (!fuel vs. run_context fuel unit.cu_context vs =
             run_context fuel (prune_unit_fcg_unreachable unit fcg).cu_context vs) /\
  !vs. mem_inv M unit.cu_context vs ==>
       mem_inv M (prune_unit_fcg_unreachable unit fcg).cu_context vs
Proof
  strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  drule_all prune_unit_ctx_agree >> strip_tac >>
  `fcg_is_reachable fcg entry` by metis_tac[fcg_analyze_entry_reachable] >>
  conj_tac
  >- (rpt gen_tac >> irule run_context_ctx_agree >>
      simp[prune_unit_fcg_unreachable_fields] >>
      qexists_tac `fcg_is_reachable fcg` >> gvs[]) >>
  rpt gen_tac >> strip_tac >> irule mem_inv_ctx_agree >>
  simp[prune_unit_fcg_unreachable_fields] >>
  qexists_tac `fcg_is_reachable fcg` >>
  qexists_tac `unit.cu_context` >>
  gvs[] >> metis_tac[rangewise_mem_fact_ctx]
QED

(* ===== The walk ===== *)

Theorem o1_walk_callee_first:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg ==>
  ALL_DISTINCT (fcg_postorder fcg entry) /\
  (!n. MEM n (fcg_postorder fcg entry) <=>
       MEM n (ctx_fn_names (prune_unit_fcg_unreachable unit fcg).cu_context)) /\
  callee_first (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions
Proof
  strip_tac >>
  `ctx_wf unit.cu_context /\ wf_invoke_targets unit.cu_context` by
    metis_tac[o1_ctx_shape_wf] >>
  conj_tac >- simp[fcg_postorder_all_distinct] >>
  conj_tac >- metis_tac[postorder_pruned_names] >>
  simp[callee_first_def, MEM_prune_unit_fcg_unreachable_functions] >>
  rpt gen_tac >> strip_tac >>
  drule_all member_invoke_direct_call >> strip_tac >>
  gvs[] >> simp[list_precedes_iff] >>
  metis_tac[fcg_postorder_callee_before_caller]
QED

(* The nine stage contexts of the walk, composed. *)
Theorem o1_walk_stages_sim:
  (!k. k < LENGTH o1_fn_passes ==>
       ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
         (stage k) (stage (SUC k))) /\
  (!k. k <= LENGTH o1_fn_passes ==> o1_ctx_shape (stage k)) /\
  (!k. k <= LENGTH o1_fn_passes ==> EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  o1_run_state_ok vs /\ o1_inv 0 (stage 0) vs ==>
  ctx_sim (stage 0) (stage (LENGTH o1_fn_passes)) vs vs /\
  o1_inv (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs
Proof
  strip_tac >>
  `!k. k < LENGTH o1_fn_passes /\ o1_inv k (stage k) vs ==>
       ctx_sim (stage k) (stage (SUC k)) vs vs /\
       o1_inv (SUC k) (stage (SUC k)) vs` by
    (rpt gen_tac >> strip_tac >>
     `o1_run_contract rpolicy k` by simp[o1_run_contracts] >>
     gvs[o1_run_contract_def, o1_stage_contract_def, o1_pre_def] >>
     `k <= LENGTH o1_fn_passes /\ SUC k <= LENGTH o1_fn_passes` by simp[] >>
     `EVERY (o1_fn_row k) (stage k).ctx_functions /\
      EVERY (o1_fn_row (SUC k)) (stage (SUC k)).ctx_functions` by simp[] >>
     first_x_assum (qspecl_then [`stage k`, `stage (SUC k)`, `vs`] mp_tac) >>
     simp[]) >>
  `LENGTH o1_fn_passes = 9` by simp[o1_fn_passes_def] >>
  gvs[] >>
  `!n. n < 9 ==>
       ctx_sim (stage 0) (stage (SUC n)) vs vs /\
       o1_inv (SUC n) (stage (SUC n)) vs` by
    (Induct
     >- (strip_tac >> first_x_assum irule >> simp[]) >>
     strip_tac >> gvs[] >>
     `ctx_sim (stage (SUC n)) (stage (SUC (SUC n))) vs vs /\
      o1_inv (SUC (SUC n)) (stage (SUC (SUC n))) vs` by
       (first_x_assum irule >> simp[]) >>
     metis_tac[ctx_sim_trans]) >>
  first_x_assum (qspec_then `8` mp_tac) >> simp[]
QED

Theorem o1_walk_sim:
  fcg = fcg_analyze unit.cu_context /\ o1_ctx_shape unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  reachable_fcg_acyclic unit.cu_context fcg /\
  ALL_DISTINCT (unit_label_namespace unit) /\
  run_callee_first rpolicy o1_fn_passes (fcg_postorder fcg entry)
    (prune_unit_fcg_unreachable unit fcg) s = SOME (unit', s') /\
  ir_supply_inst_ok s ==>
  o1_ctx_shape unit'.cu_context /\
  unit'.cu_context.ctx_entry = SOME entry /\
  ctx_fn_names unit'.cu_context =
    ctx_fn_names (prune_unit_fcg_unreachable unit fcg).cu_context /\
  !vs. o1_run_state_ok vs /\
       o1_src_inv (prune_unit_fcg_unreachable unit fcg).cu_context vs ==>
       ctx_sim (prune_unit_fcg_unreachable unit fcg).cu_context
               unit'.cu_context vs vs /\
       o1_lowered_inv unit'.cu_context vs
Proof
  strip_tac >> drule_all o1_ctx_shape_prune >> strip_tac >>
  drule_all o1_walk_callee_first >> strip_tac >>
  fs[run_callee_first_def] >>
  drule_at (Pos (el 2)) o1_schedule_stages >>
  impl_tac >- simp[o1_fn_passes_steps] >> strip_tac >>
  `o1_ctx_shape unit'.cu_context /\
   unit'.cu_context.ctx_entry = SOME entry /\
   ctx_fn_names unit'.cu_context =
     ctx_fn_names (prune_unit_fcg_unreachable unit fcg).cu_context` by
    (qpat_x_assum `!k. k <= _ ==> _` (qspec_then `LENGTH o1_fn_passes` mp_tac) >>
     gvs[prune_unit_fcg_unreachable_fields]) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `o1_inv 0 = o1_src_inv /\ o1_inv (LENGTH o1_fn_passes) = o1_lowered_inv` by
    simp[o1_inv_def, o1_fn_passes_def] >>
  `ctx_sim (stage 0) (stage (LENGTH o1_fn_passes)) vs vs /\
   o1_inv (LENGTH o1_fn_passes) (stage (LENGTH o1_fn_passes)) vs` by
    (irule o1_walk_stages_sim >> fs[] >> qexists_tac `rpolicy` >>
     rpt strip_tac >> first_x_assum drule >> simp[o1_walk_view_def]) >>
  gvs[] >> metis_tac[]
QED

(* ===== The pipeline ===== *)

Theorem o1_pipeline_stage_facts:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
  unit_entry_no_params unit /\ unit_first_block_no_phi unit ==>
  o1_ctx_shape out.po_unit.cu_context /\
  entry_fn_first out.po_unit.cu_context /\
  !vs. o1_run_state_ok vs /\ o1_src_inv unit.cu_context vs ==>
       ctx_sim unit.cu_context out.po_unit.cu_context vs vs /\
       o1_lowered_inv out.po_unit.cu_context vs
Proof
  strip_tac >> drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)`
    by simp[irSupplyTheory.init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  drule_at (Pos (el 6)) o1_walk_sim >> impl_tac
  >- (gvs[] >> metis_tac[unit_labels_wf_namespace]) >> strip_tac >>
  simp[] >> conj_tac
  >- (`entry_fn_first pre.cu_context` by
        metis_tac[source_entry_first, entry_fn_first_names] >>
      `entry_fn_first
         (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context` by
        (simp[prune_unit_fcg_unreachable_def] >>
         irule entry_fn_first_filter >> simp[] >>
         metis_tac[fcg_analyze_entry_reachable, o1_ctx_shape_wf]) >>
      irule entry_fn_first_names >>
      qexists_tac `(prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context` >>
      gvs[prune_unit_fcg_unreachable_fields]) >>
  rpt gen_tac >> strip_tac >>
  `ctx_sim unit.cu_context pre.cu_context vs vs /\
   o1_src_inv pre.cu_context vs` by metis_tac[] >>
  `(!fuel vs. run_context fuel pre.cu_context vs =
      run_context fuel (prune_unit_fcg_unreachable pre
        (fcg_analyze pre.cu_context)).cu_context vs) /\
   !vs. mem_inv raw_mem_ok pre.cu_context vs ==>
     mem_inv raw_mem_ok (prune_unit_fcg_unreachable pre
       (fcg_analyze pre.cu_context)).cu_context vs` by
    (irule o1_prune_sim >> metis_tac[rangewise_raw_mem_ok]) >>
  `o1_src_inv (prune_unit_fcg_unreachable pre
                 (fcg_analyze pre.cu_context)).cu_context vs` by
    fs[o1_src_inv_def] >>
  `ctx_sim unit.cu_context
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context vs vs` by
    (irule ctx_sim_run_context_eq >> qexists_tac `pre.cu_context` >> simp[]) >>
  metis_tac[ctx_sim_trans]
QED

Theorem o1_ctx_shape_unit_shape_ok:
  o1_ctx_shape unit.cu_context /\ entry_fn_first unit.cu_context ==>
  unit_shape_ok unit
Proof
  strip_tac >>
  `EVERY (o1_fn_shape unit.cu_context) unit.cu_context.ctx_functions` by
    gvs[o1_ctx_shape_def] >>
  drule_all entry_shape_from_members >>
  simp[unit_shape_ok_def] >>
  gvs[EVERY_MEM, o1_fn_shape_def]
QED
