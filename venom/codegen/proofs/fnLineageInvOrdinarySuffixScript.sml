Theory fnLineageInvOrdinarySuffix
Ancestors fnLineageInvSupport fnPlanLineageInventory livenessProofs cfgAnalysisProps venomWf venomExecProps stackPlanGen list rich_list cfgDefs stackPlanTypes codegenReadyCompute

(* Kept in the new task-owned theory to respect the edit boundary. *)
Theorem analyzed_nop_live_identity:
  !fn bb i.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\ (EL i bb.bb_instructions).inst_opcode = NOP ==>
    live_vars_at (liveness_analyze fn) bb.bb_label i =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[MEM_EL]) >>
  `(EL i bb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  `(EL i bb.bb_instructions).inst_operands = []` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  drule livenessProofsTheory.live_vars_at_transfer >>
  disch_then (qspecl_then [`bb.bb_label`,`bb`,`i`] mp_tac) >>
  simp[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
       venomInstTheory.inst_uses_def, venomInstTheory.inst_defs_def,
       livenessDefsTheory.ordered_inst_uses_def,
       venomInstTheory.python_stack_operands_def, venomInstTheory.operand_vars_def]
QED

(* Diagnostic: lineage_core does not promise that the selected core is
   marker-free, even together with residual_budget_wf. *)
Theorem ordinary_suffix_core_interface_probe:
  lineage_inventory {} ((init_cleanup_plan_state NONE [] 0 0) with
    ps_stack := [dead_stack_marker]) /\
  lineage_core 0 [dead_stack_marker] ((init_cleanup_plan_state NONE [] 0 0) with
    ps_stack := [dead_stack_marker]) /\
  residual_budget_wf 0 [] ((init_cleanup_plan_state NONE [] 0 0) with
    ps_stack := [dead_stack_marker]) /\
  ~(set [dead_stack_marker] SUBSET ({} : operand set))
Proof
  conj_tac
  >- (simp[lineage_inventory_def] >> qexists_tac `1` >>
      EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[] >> gen_tac >> IF_CASES_TAC >> simp[]
QED

(* The inventory witness is already distinct and disjoint from spills;
   only the stack-independent resource clauses need transporting. *)
Theorem lineage_inventory_canonical_budget:
  !S ps m core base.
    lineage_inventory S ps /\ lineage_core m core ps /\
    residual_budget_wf base [] (ps with ps_stack := core) ==>
    ?n tail. lineage_core n tail ps /\ EVERY is_var_operand tail /\
      set tail UNION FDOM ps.ps_spilled = S /\
      residual_budget_wf base [] (ps with ps_stack := tail)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lineage_inventory _ ps` mp_tac >>
  simp[lineage_inventory_def] >> strip_tac >>
  qexistsl_tac [`m'`, `core'`] >> simp[] >>
  irule reorderSimTheory.residual_budget_wf_canonical >>
  gvs[reorderSimTheory.residual_budget_wf_def]
QED
