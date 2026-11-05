Theory fnPlanLineageCallers
Ancestors
  fnPlanLineageSetup fnPlanLineageDemand fnPlanLineagePath fnPlanLineageDemandSupport
  livenessProofs cfgAnalysisProps venomWf stackPlanGen asmIR codegenReadyCompute
  passSharedDefs venomInst list rich_list

Theorem compute_operands_inst_uses:
  !inst v. MEM (Var v) (compute_operands inst) ==> MEM v (inst_uses inst)
Proof
  rpt gen_tac >>
  simp[compute_operands_def, inst_uses_def, MEM_operand_vars_eq_Var] >>
  IF_CASES_TAC
  >- simp[asmIRTheory.get_non_label_operands_def, MEM_FILTER] >>
  IF_CASES_TAC
  >- (Cases_on `inst.inst_operands` >> simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem analyzed_computed_operand_demand:
  !fn bb i v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
     (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
      ~MEM v (EL i bb.bb_instructions).inst_outputs)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, venomInstTheory.fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label i =
    liveness_transfer fn.fn_blocks (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >> simp[]) >>
  gvs[livenessDefsTheory.liveness_transfer_def, livenessDefsTheory.live_update_def,
      MEM_FILTER, MEM_APPEND, venomInstTheory.inst_defs_def] >>
  metis_tac[compute_operands_inst_uses, livenessDefsTheory.MEM_ordered_inst_uses]
QED

(* Exact copies of genBlockSim's local helper and readiness boundary.
   Importing that frame-level theory here would cross the planner boundary. *)
Theorem all_distinct_flat_map_member[local]:
  !f xs x.
    ALL_DISTINCT (FLAT (MAP f xs)) /\ MEM x xs ==>
    ALL_DISTINCT (f x)
Proof
  gen_tac >> Induct >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem codegen_ready_inst_outputs_distinct:
  !fn inst.
    codegen_ready_fn fn /\ MEM inst (fn_insts fn) ==>
    ALL_DISTINCT inst.inst_outputs
Proof
  rpt strip_tac >>
  fs[codegen_ready_fn_def, ssa_form_def] >>
  metis_tac[all_distinct_flat_map_member]
QED

(* Exact copy from unitShapeDefs, avoiding compiler-level imports. *)
Theorem MEM_fn_insts_blocks_iff[local]:
  !bbs inst. MEM inst (fn_insts_blocks bbs) <=>
             ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem ordinary_position_invariant:
  !fn bb i dfg cfg halting term lbl ps m core base ops qs.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode <> PHI /\
    (EL i bb.bb_instructions).inst_opcode <> JMP /\
    EVERY (\x. x <> dead_stack_marker) (compute_operands (EL i bb.bb_instructions)) /\
    ps.ps_stack = REPLICATE m dead_stack_marker ++ core /\
    residual_budget_wf base [] (ps with ps_stack := core) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
      demand_available fn bb i v) /\
    generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn
      (EL i bb.bb_instructions)
      (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting term lbl ps = (ops,qs)
    ==>
    (?rest. lineage_core m rest qs /\
      residual_budget_wf base [] (qs with ps_stack := rest)) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
      MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) /\
    (!v. MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled ==>
      demand_available fn bb (SUC i) v)
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn /\ wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  `ALL_DISTINCT (EL i bb.bb_instructions).inst_outputs` by
    metis_tac[codegen_ready_inst_outputs_distinct] >>
  `LENGTH (compute_operands (EL i bb.bb_instructions)) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) \/
      (MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) /\
       ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    metis_tac[analyzed_computed_operand_demand] >>
  `!v. MEM (Var v) (compute_operands (EL i bb.bb_instructions)) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by metis_tac[] >>
  drule_all definition_support_output_fresh >> strip_tac >>
  `EVERY (\v. ~MEM (Var v) (compute_operands (EL i bb.bb_instructions)) /\
     ~MEM (Var v) core /\ Var v NOTIN FDOM ps.ps_spilled)
     (EL i bb.bb_instructions).inst_outputs` by
    (gvs[EVERY_MEM, MEM_APPEND] >> metis_tac[]) >>
  conj_tac
  >- (drule_all native_regular_core_resource >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all native_regular_live_lower >> simp[]) >>
  ho_match_mp_tac native_regular_variable_support >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`m`, `core`] >>
  goal_assum (drule_at (Pat `residual_budget_wf _ _ _`)) >> simp[] >>
  gen_tac >> strip_tac
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> simp[])
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> metis_tac[])
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> metis_tac[])
  >- (irule demand_available_mono >> qexists_tac `i` >> simp[] >>
      first_x_assum irule >> metis_tac[]) >>
  irule current_output_demand_available_suc >> simp[]
QED
