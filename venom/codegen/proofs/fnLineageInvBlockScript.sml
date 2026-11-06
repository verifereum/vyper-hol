Theory fnLineageInvBlock
Ancestors fnLineageInvOrdinarySuffix fnLineageInvSupport fnPlanLineageSetup fnPlanLineageCallers stackPlanGen list rich_list pred_set

Theorem analyzed_parameter_entry_block_inventory:
 !fn bb dfg ch growth base ctr ops qs.
 codegen_ready_fn fn /\ fn.fn_blocks <> [] /\
 bb = HD fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
 LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1 /\
 ~bb_is_halting bb /\
 EVERY (\inst. inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP)
   (non_param_insts bb) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
   (init_cleanup_plan_state ch growth base ctr) = SOME (ops,qs)
 ==>
 lineage_inventory
   (set (MAP Var (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH bb.bb_instructions)))) qs /\
 (?m core. lineage_core m core qs /\
   residual_budget_wf base [] (qs with ps_stack := core))
Proof
 rpt gen_tac >> strip_tac >>
 `MEM bb fn.fn_blocks` by (Cases_on `fn.fn_blocks` >> gvs[]) >>
 drule_all ready_block_parameter_suffix >> disch_tac >>
 `non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions` by
   (qpat_assum `bb.bb_instructions = _ ++ _`
      (mp_tac o Q.AP_TERM `DROP (LENGTH (get_params bb.bb_instructions))`) >>
    simp[DROP_LENGTH_APPEND]) >>
 `LENGTH (get_params bb.bb_instructions) <= LENGTH bb.bb_instructions` by
   (qpat_assum `bb.bb_instructions = _ ++ _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]) >>
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
 irule (INST_TYPE [alpha |-> ``:cfg_analysis``] analyzed_ordinary_suffix_inventory) >> simp[] >>
 qexistsl_tac [`cfg_analyze fn`, `dfg`, `0`, `inst_ops`,
   `LENGTH (get_params (HD fn.fn_blocks).bb_instructions)`, `r`] >>
 gvs[EVERY_MEM] >> metis_tac[]
QED
