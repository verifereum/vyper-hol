Theory fnLineageInvBlock
Ancestors fnLineageInvSetupSuffix fnLineageInvOrdinarySuffix fnLineageInvSupport fnPlanLineageSetup fnPlanLineageCallers fnPlanLineageDemandSupport fnPlanPrefix fnLineageInvEdgeFacts stackPlanGen list rich_list pred_set

Theorem analyzed_parameter_entry_block_inventory:
 !fn bb dfg ch growth base ctr ops qs next.
 codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
 bb = HD fn.fn_blocks /\
 lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
 fn_reachable fn bb.bb_label /\
 LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 /\
 MEM next (cfg_succs_of (cfg_analyze fn) bb.bb_label) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
   (init_cleanup_plan_state ch growth base ctr) = SOME (ops,qs)
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
   (init_cleanup_plan_state ch growth spillbase ctr)` >> gvs[AllCaseEqs()] >>
 drule_all native_parameter_lineage_inventory >>
 disch_then (qspecl_then [`ch`, `growth`, `spillbase`, `ctr`] mp_tac) >>
 asm_rewrite_tac[] >> simp[] >> disch_tac >>
 drule_all native_parameter_residual_budget >>
 disch_then (qspecl_then [`ch`, `growth`, `spillbase`, `ctr`, `[]`] mp_tac) >>
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
