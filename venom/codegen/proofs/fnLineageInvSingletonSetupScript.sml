Theory fnLineageInvSingletonSetup
Ancestors
  fnLineageInvSupport fnPlanPrefix fnPlanLineageLiveness
  livenessDefs venomExecProps stackPlanGen list pred_set

Theorem analyzed_singleton_setup_identity:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  cfg_preds_of (cfg_analyze fn) succ = [pred] /\
  cfg_succs_of (cfg_analyze fn) pred = [succ] /\
  lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) pred
      (LENGTH pb.bb_instructions)))) ps /\
  generated_plan_state_wf_marked spill_base ps ==>
  clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn sb ps = ([],ps) /\
  lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) succ 0))) ps /\
  ?m core. lineage_core m core ps /\
    !pending. residual_budget_wf spill_base pending (ps with ps_stack := core)
Proof
  strip_tac >>
  `sb.bb_label = succ` by metis_tac[lookup_block_label] >>
  `collect_phis sb.bb_instructions = []` by
    (irule ready_small_preds_no_phis >>
     qexistsl_tac [`fn`, `succ`] >> simp[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  drule_all analyzed_live_out_singleton >>
  simp[input_vars_from_def] >> disch_tac >>
  conj_tac
  >- simp[clean_stack_plan_def] >>
  `set (MAP Var (live_vars_at (liveness_analyze fn) pred
      (LENGTH pb.bb_instructions))) =
   set (MAP Var (live_vars_at (liveness_analyze fn) succ 0))` by
    metis_tac[listTheory.LIST_TO_SET_MAP] >>
  conj_tac >- gvs[] >>
  qpat_x_assum `lineage_inventory _ ps` mp_tac >>
  simp[fnPlanLineageInventoryTheory.lineage_inventory_def] >> strip_tac >>
  qexistsl_tac [`m`, `core`] >> asm_rewrite_tac[] >> gen_tac >>
  irule reorderSimTheory.residual_budget_wf_canonical >>
  gvs[generated_plan_state_wf_marked_def,
      planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]
QED

Theorem analyzed_singleton_setup_active_resources:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
  cfg_preds_of (cfg_analyze fn) succ = [pred] /\
  1 < LENGTH (cfg_succs_of (cfg_analyze fn) pred) /\
  lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) pred
      (LENGTH pb.bb_instructions)))) ps /\
  generated_plan_state_wf_marked spill_base ps /\
  clean_stack_plan (liveness_analyze fn) (cfg_analyze fn) fn sb ps = (ops,qs)
  ==>
  generated_plan_state_wf_marked spill_base qs /\
  lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) succ 0)) UNION
     FDOM ps.ps_spilled) qs /\
  ?m core. lineage_core m core qs /\
    !pending. residual_budget_wf spill_base pending (qs with ps_stack := core)
Proof
  strip_tac >>
  `collect_phis sb.bb_instructions = []` by
    (irule ready_small_preds_no_phis >>
     qexistsl_tac [`fn`, `succ`] >> simp[]) >>
  drule_all analyzed_active_cleanup_resources >>
  simp[input_vars_from_def]
QED
