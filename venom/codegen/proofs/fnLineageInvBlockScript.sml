Theory fnLineageInvBlock
Ancestors fnPlanLineageDemand fnPlanLineageInventory stackPlanTypes stackPlanOps fnLineageInvSetupSuffix fnLineageInvOrdinarySuffix fnLineageInvSupport fnPlanLineageSetup fnPlanLineageCallers fnPlanLineageDemandSupport fnPlanPrefix fnLineageInvEdgeFacts stackPlanGen list rich_list pred_set

Theorem analyzed_parameter_entry_block_inventory:
 !fn bb dfg ch growth base ctr ops qs next promise.
 codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
 bb = HD fn.fn_blocks /\
 lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
 fn_reachable fn bb.bb_label /\
 LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 /\
 MEM next (cfg_succs_of (cfg_analyze fn) bb.bb_label) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
   ((init_cleanup_plan_state ch growth base ctr) with ps_cleanup_promised := promise) = SOME (ops,qs)
 ==>
 lineage_inventory
   (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)))) qs /\
 (?m core. lineage_core m core qs /\ EVERY is_var_operand core /\
   residual_budget_wf base [] (qs with ps_stack := core))
Proof
 rpt gen_tac >> strip_tac >>
 drule_all ready_outgoing_terminal_shape >> strip_tac >>
 `MEM bb fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
 `cfg_preds_of (cfg_analyze fn) bb.bb_label = []` by
   metis_tac[ready_entry_no_clean] >>
 `collect_phis bb.bb_instructions = []` by
   (irule ready_small_preds_no_phis >>
    qexistsl_tac [`fn`, `bb.bb_label`] >> simp[]) >>
 `EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions` by
   (simp[EVERY_MEM, MEM_EL] >> rpt strip_tac >>
    `bb_well_formed bb` by metis_tac[codegen_ready_fn_def, venomWfTheory.wf_function_def] >>
    gvs[] >> drule_all block_phi_mem_collect >> simp[]) >>
 drule_all ready_block_parameter_suffix >> disch_tac >>
 `non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions` by
   (qpat_assum `bb.bb_instructions = _ ++ _`
      (mp_tac o Q.AP_TERM `DROP (LENGTH (get_params bb.bb_instructions))`) >>
    simp[DROP_LENGTH_APPEND]) >>
 `LENGTH (get_params bb.bb_instructions) <= LENGTH bb.bb_instructions` by
   (qpat_assum `bb.bb_instructions = _ ++ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
 `EVERY (\inst. inst.inst_opcode = PHI \/ is_param_opcode inst.inst_opcode)
    (TAKE (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions)` by
   (qpat_assum `bb.bb_instructions = _ ++ _`
      (mp_tac o Q.AP_TERM `TAKE (LENGTH (get_params bb.bb_instructions))`) >>
    disch_then (fn th => pure_once_rewrite_tac[th]) >>
    pure_rewrite_tac[TAKE_LENGTH_APPEND] >>
    qspec_tac (`bb.bb_instructions`, `insts`) >>
    Induct >> simp[get_params_def] >>
    rpt strip_tac >> IF_CASES_TAC >> simp[]) >>
 qpat_x_assum `bb.bb_instructions = _ ++ _` kall_tac >>
 qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_block_plan_def, AllCaseEqs()] >> strip_tac >>
 rename1 `init_cleanup_plan_state ch growth spillbase ctr` >>
 Cases_on `prepare_params_plan (liveness_analyze fn) fn
   ((init_cleanup_plan_state ch growth spillbase ctr) with ps_cleanup_promised := promise)` >> gvs[AllCaseEqs()] >>
 drule_all ready_parameter_names_distinct >> strip_tac >>
 drule_all post_parameter_demand_ready >> strip_tac >>
 qspecl_then [`liveness_analyze fn`, `fn`,
   `(init_cleanup_plan_state ch growth spillbase ctr) with ps_cleanup_promised := promise`]
   mp_tac prepare_params_plan_inventory >>
 asm_rewrite_tac[] >>
 simp[init_cleanup_plan_state_def, init_plan_state_def] >> strip_tac >>
 `lineage_inventory
    (set (MAP Var (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))))) r` by
   (simp[lineage_inventory_def] >> qexistsl_tac [`0`, `r.ps_stack`] >>
    simp[lineage_core_def, EVERY_MEM] >>
    gvs[EXTENSION, MEM_MAP] >> metis_tac[is_var_operand_def]) >>
 drule_all fnLineageInvSupportTheory.native_parameter_residual_budget >>
 disch_then (qspecl_then [`ch`, `growth`, `spillbase`, `ctr`, `[]`, `promise`] mp_tac) >>
 asm_rewrite_tac[] >> simp[] >> disch_tac >>
 `?m core. lineage_core m core r /\
    residual_budget_wf spillbase [] (r with ps_stack := core)` by
   (qexistsl_tac [`0`, `r.ps_stack`] >> simp[fnPlanLineageInventoryTheory.lineage_core_def]) >>
 `EVERY (\inst. ~is_param_opcode inst.inst_opcode)
   (DROP (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))
      (HD fn.fn_blocks).bb_instructions)` by
   (qpat_x_assum `non_param_insts _ = _` (fn th => rewrite_tac[GSYM th]) >>
    simp[non_param_insts_def, EVERY_MEM, MEM_FILTER]) >>
 irule (INST_TYPE [alpha |-> ``:cfg_analysis``] analyzed_outgoing_exact_suffix_inventory) >> simp[] >>
 conj_tac >- metis_tac[] >>
 qexistsl_tac [`cfg_analyze fn`, `dfg`, `0`, `inst_ops`,
   `LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`, `r`] >>
 simp[] >> conj_tac >- metis_tac[] >>
 simp[EVERY_CONJ] >> metis_tac[EVERY_DROP]
QED

Theorem analyzed_singleton_outgoing_block_inventory:
 !fn pred succ pb sb next ps base dfg ops qs.
 codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\ sb <> HD fn.fn_blocks /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 cfg_preds_of (cfg_analyze fn) succ = [pred] /\
 MEM next (cfg_succs_of (cfg_analyze fn) succ) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred
   (LENGTH pb.bb_instructions)))) ps /\
 generated_plan_state_wf_marked base ps /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb ps = SOME (ops,qs)
 ==>
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) sb.bb_label
   (LENGTH sb.bb_instructions)))) qs /\
 (?m core. lineage_core m core qs /\ EVERY is_var_operand core /\
   residual_budget_wf base [] (qs with ps_stack := core))
Proof
 rpt gen_tac >> strip_tac >>
 `sb.bb_label = succ` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
 `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
 drule_all nonentry_block_no_params >> strip_tac >>
 drule_all ready_outgoing_terminal_shape >> strip_tac >>
 `MEM sb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
 `bb_well_formed sb` by metis_tac[codegen_ready_fn_def, venomWfTheory.wf_function_def] >>
 `collect_phis sb.bb_instructions = []` by
   (irule ready_small_preds_no_phis >> qexistsl_tac [`fn`, `succ`] >> simp[]) >>
 `EVERY (\inst. inst.inst_opcode <> PHI) sb.bb_instructions` by
   (simp[EVERY_MEM, MEM_EL] >> rpt strip_tac >> gvs[] >>
    drule_all block_phi_mem_collect >> simp[]) >>
 `EVERY (\inst. ~is_param_opcode inst.inst_opcode) sb.bb_instructions` by
   (qpat_x_assum `non_param_insts sb = _` mp_tac >>
    simp[non_param_insts_def, FILTER_EQ_ID, EVERY_MEM]) >>
 qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
 simp[generate_block_plan_def] >> pairarg_tac >> simp[AllCaseEqs()] >> strip_tac >>
 Cases_on `1 < LENGTH (cfg_succs_of (cfg_analyze fn) pred)`
 >- (`EVERY (\inst. inst.inst_opcode <> PHI /\ ~is_param_opcode inst.inst_opcode)
        sb.bb_instructions` by simp[EVERY_CONJ] >>
     gvs[] >>
     drule_all fnLineageInvSetupSuffixTheory.analyzed_active_singleton_suffix_replay >>
     disch_then (qspec_then `0` mp_tac) >>
     `0 < LENGTH sb.bb_instructions` by (Cases_on `sb.bb_instructions` >> gvs[]) >>
     simp[] >> strip_tac >> simp[] >> metis_tac[]) >>
 `cfg_succs_of (cfg_analyze fn) pred = [succ]` by
   (Cases_on `cfg_succs_of (cfg_analyze fn) pred` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
 drule_all fnLineageInvSingletonSetupTheory.analyzed_singleton_setup_identity >>
 strip_tac >> gvs[] >>
 `fn_reachable fn sb.bb_label` by
   metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze,
     codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
     venomExecProofsTheory.fn_reachable_step, codegen_ready_fn_def, MEM] >>
 irule (INST_TYPE [alpha |-> ``:cfg_analysis``] analyzed_outgoing_exact_suffix_inventory) >>
 simp[] >> conj_tac >- metis_tac[] >>
 qexistsl_tac [`cfg_analyze fn`, `dfg`, `0`, `inst_ops`, `0`, `ps`] >>
 simp[EVERY_CONJ] >> metis_tac[]
QED

Theorem analyzed_join_outgoing_block_inventory:
 !fn entry pred pb succ sb next dfg ps0 pops ps m core base ops qs.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\ sb <> HD fn.fn_blocks /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 cfg_succs_of (cfg_analyze fn) pred = [succ] /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 cfg_reachable_of (cfg_analyze fn) pred /\
 MEM next (cfg_succs_of (cfg_analyze fn) succ) /\
 (?A. generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 = SOME (pops,A) /\
      ps.ps_stack = A.ps_stack /\ ps.ps_spilled = A.ps_spilled) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred
   (LENGTH pb.bb_instructions)))) ps /\
 lineage_core m core ps /\ EVERY is_var_operand core /\
 residual_budget_wf base [] (ps with ps_stack := core) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn sb ps = SOME (ops,qs)
 ==>
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) sb.bb_label
   (LENGTH sb.bb_instructions)))) qs /\
 (?n tail. lineage_core n tail qs /\ EVERY is_var_operand tail /\
   residual_budget_wf base [] (qs with ps_stack := tail))
Proof
 rpt gen_tac >> strip_tac >>
 `sb.bb_label = succ` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
 `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
 drule_all nonentry_block_no_params >> strip_tac >>
 drule_all ready_outgoing_terminal_shape >> strip_tac >>
 `MEM sb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
 `bb_well_formed sb` by metis_tac[codegen_ready_fn_def, venomWfTheory.wf_function_def] >>
 `EVERY (\inst. ~is_param_opcode inst.inst_opcode) sb.bb_instructions` by
   (qpat_x_assum `non_param_insts sb = _` mp_tac >>
    simp[non_param_insts_def, FILTER_EQ_ID, EVERY_MEM]) >>
 `LENGTH (collect_phis sb.bb_instructions) <= LENGTH sb.bb_instructions /\
  TAKE (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions = collect_phis sb.bb_instructions` by
   (qspec_then `sb.bb_instructions` strip_assume_tac fnPlanLineageLivenessTheory.collect_phis_prefix >>
    conj_tac
    >- (qpat_assum `sb.bb_instructions = _ ++ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
    qpat_assum `sb.bb_instructions = _ ++ _`
      (mp_tac o Q.AP_TERM `TAKE (LENGTH (collect_phis sb.bb_instructions))`) >>
    simp[TAKE_LENGTH_APPEND]) >>
 qpat_x_assum `generate_block_plan _ _ _ _ sb _ = _` mp_tac >>
 simp[generate_block_plan_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
 qsuff_tac `LENGTH (collect_phis sb.bb_instructions) < LENGTH sb.bb_instructions \/
  LENGTH sb.bb_instructions = LENGTH (collect_phis sb.bb_instructions)`
 >- (disch_tac >>
     drule_all (SRULE [] (GEN_ALL (Q.INST
       [`k` |-> `LENGTH (collect_phis sb.bb_instructions)`]
       (SPEC_ALL analyzed_join_actual_phi_residual_inventory)))) >> strip_tac >>
     `EVERY (\inst. inst.inst_opcode <> PHI)
       (DROP (LENGTH (collect_phis sb.bb_instructions)) sb.bb_instructions)` by
       (qpat_x_assum `bb_well_formed sb` mp_tac >>
        simp[venomWfTheory.bb_well_formed_def] >> strip_tac >>
        qpat_x_assum `!i j. _` mp_tac >>
        qspec_tac (`sb.bb_instructions`, `insts`) >>
        Induct >> simp[livenessDefsTheory.collect_phis_def] >>
        rpt strip_tac >> Cases_on `h.inst_opcode = PHI`
        >- (simp[] >> first_x_assum irule >> rpt strip_tac >>
            qpat_x_assum `!i j. _` (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
        `EVERY (\inst. inst.inst_opcode <> PHI) (h::insts)` by
          (simp[EVERY_EL] >> rpt strip_tac >>
           qpat_x_assum `!i j. _` (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
        metis_tac[EVERY_DROP]) >>
     irule (INST_TYPE [alpha |-> ``:cfg_analysis``] analyzed_outgoing_exact_suffix_inventory) >>
     simp[] >> conj_tac >- metis_tac[] >>
     qexistsl_tac [`cfg_analyze fn`, `dfg`, `LENGTH (collect_phis sb.bb_instructions)`,
       `post`, `0`, `qs'`] >>
     simp[EVERY_CONJ] >> rpt conj_tac
     >- (simp[EVERY_MEM] >> metis_tac[livenessProofsTheory.collect_phis_mem])
     >- metis_tac[EVERY_DROP] >>
     simp[EVERY_MEM] >> metis_tac[livenessProofsTheory.collect_phis_mem]) >> decide_tac
QED
