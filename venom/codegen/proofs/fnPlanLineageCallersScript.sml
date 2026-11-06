Theory fnPlanLineageCallers
Ancestors
  fnPlanLineageSetup fnPlanLineageDemand fnPlanLineagePath fnPlanLineageDemandSupport
  livenessProofs cfgAnalysisProps venomWf stackPlanGen asmIR codegenReadyCompute
  passSharedDefs venomInst callLayoutDefs list rich_list

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
  gvs[livenessDefsTheory.liveness_transfer_def, livenessProofsTheory.live_update_mem,
      venomInstTheory.inst_defs_def] >>
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

Theorem param_insts_from_filter[local]:
  !params k. param_insts_from k params ==>
    FILTER (\inst. ~is_param_opcode inst.inst_opcode) params = []
Proof
  Induct >> simp[param_insts_from_def, param_inst_at_def] >>
  rpt strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem ready_block_parameter_suffix:
  !fn bb. codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
    bb.bb_instructions = get_params bb.bb_instructions ++ non_param_insts bb
Proof
  rpt gen_tac >> strip_tac >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `canonical_param_prefix fn` mp_tac >>
  rewrite_tac[canonical_param_prefix_iff] >>
  disch_then (qx_choose_then `entry` (qx_choose_then `rest`
    (qx_choose_then `users` (qx_choose_then `fmp` (qx_choose_then `retpc`
      (qx_choose_then `tail_insts` (map_every assume_tac o CONJUNCTS))))))) >>
  Cases_on `bb = entry`
  >- (gnvs[] >>
      `get_params ((users ++ fmp ++ retpc) ++ tail_insts) = users ++ fmp ++ retpc` by
        (irule get_params_canonical_prefix >> simp[] >> metis_tac[]) >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) (users ++ fmp ++ retpc) = []` by
        metis_tac[param_insts_from_filter] >>
      `FILTER (\inst. ~is_param_opcode inst.inst_opcode) tail_insts = tail_insts` by
        gvs[FILTER_EQ_ID, no_param_insts_def] >>
      simp[non_param_insts_def] >>
      qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[th]) >>
      once_rewrite_tac[APPEND_ASSOC] >>
      simp[FILTER_APPEND]) >>
  `MEM bb rest` by gvs[] >>
  `no_param_insts bb.bb_instructions` by
    (qpat_x_assum `EVERY _ rest` mp_tac >> simp[EVERY_MEM]) >>
  `get_params bb.bb_instructions = []` by
    (Cases_on `bb.bb_instructions` >> gvs[no_param_insts_def, get_params_def]) >>
  simp[non_param_insts_def, FILTER_EQ_ID] >> gvs[no_param_insts_def]
QED

Theorem ready_block_suffix_index:
  !fn bb k. codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH (non_param_insts bb) ==>
    EL k (non_param_insts bb) =
      EL (LENGTH (get_params bb.bb_instructions) + k) bb.bb_instructions
Proof
  rpt strip_tac >> drule_all ready_block_parameter_suffix >>
  disch_then (fn th => CONV_TAC (RHS_CONV (RAND_CONV (REWR_CONV th)))) >>
  simp[EL_APPEND2]
QED

Theorem ready_block_suffix_next_live:
  !fn bb lv k inst rest.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    DROP k (non_param_insts bb) = inst::rest /\
    k < LENGTH (non_param_insts bb) ==>
    (if rest = [] then live_vars_at lv bb.bb_label (LENGTH bb.bb_instructions)
     else live_vars_at lv bb.bb_label (k + LENGTH (get_params bb.bb_instructions) + 1)) =
    live_vars_at lv bb.bb_label (SUC (LENGTH (get_params bb.bb_instructions) + k))
Proof
  rpt strip_tac >>
  `LENGTH bb.bb_instructions = LENGTH (get_params bb.bb_instructions) +
      LENGTH (non_param_insts bb)` by
    metis_tac[ready_block_parameter_suffix, LENGTH_APPEND] >>
  reverse (Cases_on `rest = []`)
  >- (simp[] >> AP_TERM_TAC >> decide_tac) >>
  simp[] >>
  `LENGTH (non_param_insts bb) - k = 1` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[]) >>
  `LENGTH bb.bb_instructions = SUC (LENGTH (get_params bb.bb_instructions) + k)` by
    decide_tac >> AP_TERM_TAC >> decide_tac
QED

Theorem analyzed_entry_prefix_support:
  !fn bb n v.
    codegen_ready_fn fn /\ entry_block fn = SOME bb /\
    n <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label n) ==>
    demand_available fn bb n v
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn.fn_blocks <> [] /\ bb = HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `MEM bb fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `fn_reachable fn bb.bb_label` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_reachable_def, fn_entry_label_def] >>
     metis_tac[relationTheory.RTC_REFL]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecProofsTheory.MEM_lookup_block >>
     gvs[wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    (drule cfg_analyze_reachable_sets >> simp[pred_setTheory.EXTENSION] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `live_vars_at (liveness_analyze fn) bb.bb_label 0 = []` by
    metis_tac[analyzed_entry_live_empty] >>
  qpat_x_assum `bb = HD _` kall_tac >>
  drule_all live_prefix_demand >>
  simp[MEM_FLAT, MEM_MAP] >> strip_tac >>
  qpat_x_assum `MEM _ (TAKE _ _)` (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `j < LENGTH (TAKE n bb.bb_instructions)` >>
  `j < n /\ j < LENGTH bb.bb_instructions` by gvs[LENGTH_TAKE] >>
  `MEM v (EL j bb.bb_instructions).inst_outputs` by
    gvs[EL_TAKE, inst_defs_def] >>
  irule demand_available_mono >> qexists_tac `SUC j` >> simp[] >>
  irule current_output_demand_available_suc >> simp[]
QED

Theorem initial_parameter_definition_support:
  !fn ch growth spill_base lbl_ctr ps v.
    codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
    ps = SND (prepare_params_plan (liveness_analyze fn) fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr)) /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    demand_available fn (HD fn.fn_blocks)
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)) v
Proof
  rpt gen_tac >> strip_tac >>
  drule_all native_parameter_inventory >> strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))` by
    (gvs[pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
  `entry_block fn = SOME (HD fn.fn_blocks)` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
  `LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <=
      LENGTH (HD fn.fn_blocks).bb_instructions` by
    (drule_all ready_block_parameter_suffix >>
     disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
  irule analyzed_entry_prefix_support >> simp[]
QED

Theorem ready_entry_no_clean:
  !fn. codegen_ready_fn fn /\ fn.fn_blocks <> [] ==>
    cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []
Proof
  rpt strip_tac >> gvs[codegen_ready_fn_def, block_entries_ready_def] >>
  Cases_on `fn.fn_blocks` >> gvs[entry_block_def, NULL_EQ]
QED
