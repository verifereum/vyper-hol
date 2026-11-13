Theory fnLineageInvOrdinarySuffix
Ancestors fnLineageInvOffset fnLineageInvSupport fnPlanLineageInventory livenessProofs cfgAnalysisProps venomWf venomExecProps stackPlanGen list rich_list cfgDefs stackPlanTypes codegenReadyCompute

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

Theorem analyzed_ordinary_inst_inventory:
 !fn bb k dfg cfg term base ps ops qs.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 k < LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI) (DROP k bb.bb_instructions) /\
 (EL k bb.bb_instructions).inst_opcode <> JMP /\
 (EL k bb.bb_instructions).inst_opcode <> OFFSET /\
 ~is_param_opcode (EL k bb.bb_instructions).inst_opcode /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))) ps /\
 (?m core. lineage_core m core ps /\ residual_budget_wf base [] (ps with ps_stack := core)) /\
 generate_inst_plan (liveness_analyze fn) dfg cfg fn (EL k bb.bb_instructions)
   (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)) F term bb.bb_label ps = SOME (ops,qs)
 ==>
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC k)))) qs /\
 (?n tail. lineage_core n tail qs /\ residual_budget_wf base [] (qs with ps_stack := tail))
Proof
 rpt gen_tac >> strip_tac >>
 `(EL k bb.bb_instructions).inst_opcode <> PHI` by
   (gvs[EVERY_MEM] >> first_x_assum irule >> simp[MEM_DROP, MEM_EL] >> qexists_tac `0` >> simp[]) >>
 Cases_on `(EL k bb.bb_instructions).inst_opcode = NOP`
 >- (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def] >> strip_tac >> gvs[] >>
     drule_all analyzed_nop_live_identity >> strip_tac >> gvs[] >> metis_tac[]) >>
 drule_all lineage_inventory_canonical_budget >> strip_tac >>
 `ps.ps_stack = REPLICATE n dead_stack_marker ++ tail` by
   gvs[lineage_core_def] >>
 `set tail UNION FDOM ps.ps_spilled SUBSET
    set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label k))` by (qpat_x_assum `set tail UNION _ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
 `!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
   (gvs[pred_setTheory.EXTENSION, MEM_MAP, MEM_APPEND] >> metis_tac[]) >>
 `k <= LENGTH bb.bb_instructions` by simp[] >>
 `!v. MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled ==>
    demand_available fn bb k v` by
   (rpt strip_tac >> irule analyzed_suffix_inventory_demand >>
    simp[] >> qexistsl_tac [`tail`, `n`, `ps`] >>
    asm_rewrite_tac[] >>
    qpat_x_assum `set tail UNION _ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
 qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_inst_plan_def, AllCaseEqs()] >> strip_tac >>
 drule_all analyzed_ordinary_live_inventory >> strip_tac >>
 simp[] >> metis_tac[]
QED

Theorem analyzed_ordinary_suffix_inventory:
 !fn bb dfg cfg base p j ps ops qs.
 codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 j + p <= LENGTH bb.bb_instructions /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
   ~is_param_opcode inst.inst_opcode)
   (DROP (j+p) bb.bb_instructions) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (j+p)))) ps /\
 (?m core. lineage_core m core ps /\ residual_budget_wf base [] (ps with ps_stack := core)) /\
 generate_block_insts_plan (liveness_analyze fn) dfg cfg fn bb.bb_label F p
   (LENGTH bb.bb_instructions) j (DROP (j+p) bb.bb_instructions) ps = SOME (ops,qs)
 ==>
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)))) qs /\
 (?n tail. lineage_core n tail qs /\ residual_budget_wf base [] (qs with ps_stack := tail))
Proof
 rpt gen_tac >>
 map_every qid_spec_tac [`ps`,`ops`,`qs`,`j`] >>
 measureInduct_on `LENGTH bb.bb_instructions - (j+p)` >>
 rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
 Cases_on `j+p = LENGTH bb.bb_instructions`
 >- (gvs[DROP_LENGTH_TOO_LONG, generate_block_insts_plan_def] >> metis_tac[]) >>
 `j+p < LENGTH bb.bb_instructions` by decide_tac >>
 `DROP (j+p) bb.bb_instructions =
   EL (j+p) bb.bb_instructions :: DROP (SUC (j+p)) bb.bb_instructions` by
   simp[DROP_CONS_EL] >>
 `DROP (SUC (j+p)) bb.bb_instructions = [] ==>
    SUC (j+p) = LENGTH bb.bb_instructions` by
   (simp[DROP_EQ_NIL] >> decide_tac) >>
 qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
 once_rewrite_tac[generate_block_insts_plan_def] >>
 asm_rewrite_tac[] >>
 simp[Once generate_block_insts_plan_def, AllCaseEqs()] >> strip_tac >>
 ` (if LENGTH bb.bb_instructions <= SUC (j+p) then
      live_vars_at (liveness_analyze fn) bb.bb_label (LENGTH bb.bb_instructions)
    else live_vars_at (liveness_analyze fn) bb.bb_label (j+(p+1))) =
    live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))` by
   (IF_CASES_TAC >> simp[] >> AP_TERM_TAC >> decide_tac) >>
 gvs[] >>
 `EVERY (\inst. inst.inst_opcode <> PHI) (DROP (j+p) bb.bb_instructions)` by
   (gvs[EVERY_MEM] >> metis_tac[]) >>
 ` (EL (j+p) bb.bb_instructions).inst_opcode <> JMP /\
   ~is_param_opcode (EL (j+p) bb.bb_instructions).inst_opcode` by
   (qpat_x_assum `EVERY (\inst. _ /\ _) _` mp_tac >>
    once_asm_rewrite_tac[] >> simp[]) >>
 rename1 `residual_budget_wf spillbase [] (ps with ps_stack := core)` >>
 `lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label (SUC (j+p))))) ps' /\
  (?n tail. lineage_core n tail ps' /\
    residual_budget_wf spillbase [] (ps' with ps_stack := tail))` by
   (Cases_on `(EL (j+p) bb.bb_instructions).inst_opcode = OFFSET`
    >- suspend "offset_step" >>
    drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
      analyzed_ordinary_inst_inventory >>
    disch_then (qspec_then `spillbase` mp_tac) >>
    (impl_tac >- (simp[] >> metis_tac[])) >> simp[]) >>
 first_x_assum (qspec_then `SUC (j+p)` mp_tac) >>
 (impl_tac >- decide_tac) >>
 disch_then (qspecl_then [`j+1`,`p`] mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES] >>
 disch_then (qspecl_then [`qs`,`rest_ops`,`ps'`] mp_tac) >>
 `j+(p+1) = SUC (j+p)` by decide_tac >>
 simp[] >> metis_tac[]
QED

Resume analyzed_ordinary_suffix_inventory[offset_step]:
  `inst_wf (EL (j+p) bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[EL_MEM]) >>
  qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def] >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def,
    venomInstTheory.is_raw_fmp_opcode_def] >> strip_tac >>
  `?x. (EL (j+p) bb.bb_instructions).inst_outputs = [x]` by
    (qpat_x_assum `LENGTH _ = 1` mp_tac >>
     simp[listTheory.LENGTH_EQ_NUM_compute]) >>
  irule analyzed_offset_inventory >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Finalise analyzed_ordinary_suffix_inventory
